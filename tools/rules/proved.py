"""Which rules are proved, read from the compiled `Rules` library.

A rule is proved when `Rules.<name>` is a theorem whose type is `Rules.Stmt.<name>`, the statement generated
from the rule's source, on the standard three axioms, in a library `lake` has nothing left to build for and
`leanchecker` replays, with every module it imports but Lean's own. docs/rules.md. Only a proved rule is given
to the matcher, so the search never applies a rule whose theorem is missing, false, or rests on `sorry` or
`bv_decide`.

The checker and every `leanchecker` read the same files: a copy of the libraries, held still while they run,
the checker as it was written for them, and Lean's own modules from the toolchain that's stamped, whatever
LEAN_SYSROOT the caller set. Anything else running as the user, another build in the checkout or an editor,
could otherwise change a module between the checker reading it and the kernel replaying it. What this holds
against, and what it doesn't, is docs/rules.md's "What the gates promise".
"""

from __future__ import annotations

import concurrent.futures
import json
import os
import secrets
import shutil
import sys
import tempfile
from pathlib import Path
from typing import Any

import gen
import lang

ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.append(str(ROOT / "tools"))

from irlean import hashing, lean, proc, schemas  # noqa: E402
from irlean import verdict as core  # noqa: E402

CHECK = Path(__file__).resolve().parent / "rules_check.lean"
LEAN_MB = 4096
TIMEOUT = 900.0
MARK = "IRLEAN_RULES"
# What a rule's proof or a certificate may import besides Lean's own, as rules_check.lean allows a
# certificate. The checks read them from a copy.
LIBRARIES = ("IRLean", "Peephole", "Rules")
# The files Lean reads a module from. The repo's libraries have only `.olean`, and Lean's own all four.
MODULE_FILES = (".olean", ".olean.server", ".olean.private", ".ir")
UNCHANGED = "what the checks read didn't change while they ran"


class ToolError(RuntimeError):
    """Something this needs isn't there, or a tool answered in a way it doesn't read."""


def run(
    argv: list[str],
    env: dict[str, str] | None = None,
    cwd: Path = ROOT,
    timeout: float = TIMEOUT,
    stdin: str | None = None,
    scope: proc.Scope | None = None,
) -> proc.Ran:
    """Runs a command, under a time limit, with `stdin` as its input if given, and in `scope` if given and
    systemd can make one, which kills everything the command started when it ends, in whatever session."""
    try:
        return proc.run(argv, cwd=cwd, env=env, timeout=timeout, stdin=stdin, scope=scope)
    except FileNotFoundError as error:
        raise ToolError(f"{argv[0]} isn't on PATH: run inside nix develop") from error


def toolchain() -> Path:
    """The pinned toolchain's directory, as elan finds it: the `lean`, `leanchecker` and `lake` the checks
    run, and Lean's own modules. `lean --print-prefix` doesn't read LEAN_SYSROOT, which the toolchain's
    processes do."""
    ran = run(["lean", "--print-prefix"], lean.env(pin=True))
    if ran.exit != 0 or not ran.out.strip():
        raise ToolError(f"lean --print-prefix failed: {ran.output[-300:]}")
    return Path(ran.out.strip()).resolve()


def lean_env(prefix: Path, *dirs: Path) -> dict[str, str]:
    """The environment of each Lean process a gate starts: only `dirs` on LEAN_PATH, and LEAN_SYSROOT the
    toolchain `prefix`, the one that's stamped, so Lean's own modules are read from there and not from a
    directory a LEAN_SYSROOT the caller set names."""
    return lean.env(*dirs, library=False, pin=True, LEAN_SYSROOT=str(prefix))


def binary(env: dict[str, str], name: str) -> str:
    """The toolchain's `name`, such as `lean` or `leanchecker`, by its path in the toolchain `env`'s
    LEAN_SYSROOT names, which lean_env set."""
    return str(Path(env["LEAN_SYSROOT"]) / "bin" / name)


def copy_libraries(into: Path, overlay: Path | None = None) -> Path:
    """Copies every module of LIBRARIES into `into`, and returns it: each library from `overlay` if it has it,
    as Lean's search path finds a library in the first directory that has it, and otherwise from the repo's
    build. With `into` alone on LEAN_PATH, a check reads only these copies and the toolchain."""
    for name in LIBRARIES:
        source = next(
            (
                d
                for d in [*([overlay] if overlay else []), lean.LIBRARY]
                if (d / name).is_dir() or (d / f"{name}.olean").is_file()
            ),
            None,
        )
        if source is None:
            continue
        files = [source / f"{name}{suffix}" for suffix in MODULE_FILES]
        for directory, _, names in os.walk(source / name, followlinks=True):
            files += [Path(directory) / n for n in names]
        for path in files:
            if path.name.endswith(MODULE_FILES) and path.is_file():
                target = into / path.relative_to(source)
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(path, target)
    return into


def seal(copies: Path, *also: Path) -> dict[str, dict[str, Any]]:
    """What the checks read, as it is now: every file under `copies` by its hash, and what `lstat` says of
    `copies`, `also`, such as the toolchain, too large to hash each time, and every entry under them. Taken
    again, it differs after any write, replacement, new file or removal, even one put back, and after one of
    them is moved aside and put back: each moves a change time, which a process without root can't set back.
    `lstat` first, so a change while it hashes shows."""
    stamps = hashing.stamp(copies, *also)
    return {"lstat": stamps, "sha256": hashing.snapshot(copies)}


def unsealed(sealed: dict[str, dict[str, Any]], copies: Path, *also: Path) -> list[str]:
    """Every path whose hash or `lstat` differs from `sealed`, which `seal(copies, *also)` gave."""
    now = seal(copies, *also)
    return sorted(
        {
            p
            for kind, was in sealed.items()
            for p in was.keys() | now[kind].keys()
            if was.get(p) != now[kind].get(p)
        }
    )


def ask(
    config: dict[str, Any], header: str, env: dict[str, str], work: Path
) -> tuple[proc.Ran, list[Any], list[str]]:
    """Runs tools/rules/rules_check.lean under `header`, its imports, and returns what it answered, and each
    of the two files it wrote for Lean, the checker and its configuration, that then wasn't what it wrote, by
    hash or by `lstat`: an answer counts only if that's none, as Lean ran what was there."""
    nonce = secrets.token_hex(16)
    source, configuration = work / "RulesCheck.lean", work / "rules_check.json"
    written = {source: header + CHECK.read_text(), configuration: json.dumps({**config, "nonce": nonce})}
    for path, text in written.items():
        path.write_text(text)
    stamped = hashing.stamp(*written)
    ran = run(
        lean.argv(LEAN_MB, str(source), lean=binary(env, "lean")),
        {**env, "IRLEAN_RULES_CONFIG": str(configuration)},
        cwd=work,
    )
    changed = [
        str(path)
        for path, text in written.items()
        if not path.is_file()
        or hashing.sha256_file(path) != hashing.sha256_text(text)
        or hashing.stamp(path)[str(path)] != stamped[str(path)]
    ]
    marker = f"{MARK} {nonce} "
    answers = [json.loads(line[len(marker) :]) for line in ran.out.splitlines() if line.startswith(marker)]
    return ran, answers, changed


def replay(modules: Any, env: dict[str, str], cwd: Path = ROOT) -> core.Step:
    """`leanchecker` on each of `modules`, the ones rules_check.lean names, a few at a time, one process each,
    as tools/store/store.py runs it: one process for all of them holds an environment for each at once, 10 GB
    for the rules'. The first that didn't end on its own with 0, or the last if all did. Anything but a
    non-empty list of names is a step that didn't run, which grants nothing."""
    if not isinstance(modules, list) or not modules or not all(isinstance(m, str) and m for m in modules):
        return core.Step("leanchecker", None, output=f"no modules to replay: {modules!r}")
    jobs = max(1, min(int(os.environ.get("LEAN_JOBS", "2")), 4))
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as pool:
        ran = list(
            pool.map(
                lambda m: run(lean.checker(m, leanchecker=binary(env, "leanchecker")), env, cwd=cwd), modules
            )
        )
    steps = [core.Step.of(f"leanchecker {m}", r) for m, r in zip(modules, ran, strict=True)]
    return next((s for s in steps if s.exit != 0 or s.limit is not None), steps[-1])


def check(rules: list[lang.Rule] | None = None, overlay: Path | None = None) -> dict[str, Any]:
    """Every rule, proved or refused with why, as a record of schema RULES_PROVED. `overlay` is a directory
    holding another build of the `Rules` library and its `Rules/Statements.lean`, read in place of the repo's,
    for a test of a library that's wrong."""
    rules = gen.load_all() if rules is None else rules
    statements = gen.STATEMENTS if overlay is None else overlay / "Rules" / "Statements.lean"
    stale = not statements.exists() or statements.read_text() != gen.statements_text(rules)
    prefix = toolchain()
    if overlay is None:
        lake = [str(prefix / "bin" / "lake"), "build", "--no-build", "Rules"]
        current = run(lake, {**os.environ, "LEAN_SYSROOT": str(prefix)}).exit == 0
    else:
        current = (overlay / "Rules.olean").exists()
    with tempfile.TemporaryDirectory() as temporary:
        work = Path(temporary)
        modules = copy_libraries(work / "modules", overlay)
        held = (modules, prefix, CHECK)
        sealed = seal(*held)
        env = lean_env(prefix, modules)
        asked, answers, rewritten = ask(
            {"mode": "rules", "rules": [r.name for r in rules]}, "import Lean\n", env, work
        )
        listed = [a["replay"] for a in answers if isinstance(a, dict) and "replay" in a]
        replayed = replay(listed[0] if len(listed) == 1 else None, env)
        moved = unsealed(sealed, *held) + rewritten
    by_name = {a["rule"]: a for a in answers if isinstance(a, dict) and "rule" in a}
    out: list[dict[str, Any]] = []
    for rule in rules:
        answer = by_name.get(rule.name, {})
        checks = {
            "rules/Rules/Statements.lean is what the source generates": not stale,
            "lake has nothing left to build for Rules": current,
            f"Rules.{rule.name} states its generated statement, on the standard three axioms": answer.get(
                "ok"
            )
            is True,
            UNCHANGED: not moved,
        }
        decision = core.decide(
            core.Verdict.PROVED,
            core.Evidence(
                lean=core.Step.of("rules_check.lean", asked),
                replay=replayed,
                axioms=answer.get("ok") is True,
                checks=checks,
            ),
        )
        entry: dict[str, Any] = {
            "name": rule.name,
            "match": lang.show(rule.pattern),
            "replace": lang.show(rule.replacement),
            "where": [lang.show(c) for c in rule.conds],
            "statement_sha256": hashing.sha256_text(rule.statement()),
            "proved": decision.granted,
        }
        if decision.granted:
            entry["axioms"] = answer["axioms"]
        else:
            entry["reason"] = answer.get("reason") or decision.reason
            entry["detail"] = answer.get("detail") or decision.detail
            if moved:
                entry["detail"] += "\nchanged: " + ", ".join(moved[:20])
            if not answer.get("detail") and (replayed.exit != 0 or replayed.limit is not None):
                entry["detail"] += f"\n{replayed.name}: {replayed.output[-1000:]}"
        out.append(entry)
    return {"schema": schemas.RULES_PROVED, "rules": out}


def proved_rules() -> tuple[list[lang.Rule], dict[str, Any]]:
    """The rules a search may apply: the proved ones. And the record that says so."""
    rules = gen.load_all()
    record = check(rules)
    good = {e["name"] for e in record["rules"] if e["proved"]}
    return [r for r in rules if r.name in good], record
