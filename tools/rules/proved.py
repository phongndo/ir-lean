"""Which rules are proved, read from the compiled `Rules` library.

A rule is proved when `Rules.<name>` is a theorem whose type is `Rules.Stmt.<name>`, the statement generated
from the rule's source, on the standard three axioms, in a library `lake` has nothing left to build for and
`leanchecker` replays. docs/rules.md. Only a proved rule is given to the matcher, so the search never applies
a rule whose theorem is missing, false, or rests on `sorry` or `bv_decide`.
"""

from __future__ import annotations

import json
import secrets
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


class ToolError(RuntimeError):
    """Something this needs isn't there, or a tool answered in a way it doesn't read."""


def run(
    argv: list[str],
    env: dict[str, str] | None = None,
    cwd: Path = ROOT,
    timeout: float = TIMEOUT,
    stdin: str | None = None,
) -> proc.Ran:
    """Runs a command, under a time limit, with `stdin` as its input if given."""
    try:
        return proc.run(argv, cwd=cwd, env=env, timeout=timeout, stdin=stdin)
    except FileNotFoundError as error:
        raise ToolError(f"{argv[0]} isn't on PATH: run inside nix develop") from error


def ask(config: dict[str, Any], header: str, env: dict[str, str], work: Path) -> tuple[proc.Ran, list[Any]]:
    """Runs tools/rules/rules_check.lean under `header`, its imports, and returns what it answered."""
    nonce = secrets.token_hex(16)
    source = work / "RulesCheck.lean"
    source.write_text(header + CHECK.read_text())
    (work / "rules_check.json").write_text(json.dumps({**config, "nonce": nonce}))
    ran = run(
        lean.argv(LEAN_MB, str(source)),
        {**env, "IRLEAN_RULES_CONFIG": str(work / "rules_check.json")},
        cwd=work,
    )
    marker = f"{MARK} {nonce} "
    answers = [json.loads(line[len(marker) :]) for line in ran.out.splitlines() if line.startswith(marker)]
    return ran, answers


def check(rules: list[lang.Rule] | None = None, overlay: Path | None = None) -> dict[str, Any]:
    """Every rule, proved or refused with why, as a record of schema RULES_PROVED. `overlay` is a directory
    holding another build of the `Rules` library and its `Rules/Statements.lean`, read in place of the repo's,
    for a test of a library that's wrong."""
    rules = gen.load_all() if rules is None else rules
    statements = gen.STATEMENTS if overlay is None else overlay / "Rules" / "Statements.lean"
    stale = not statements.exists() or statements.read_text() != gen.statements_text(rules)
    if overlay is None:
        current = run(["lake", "build", "--no-build", "Rules"]).exit == 0
        env = lean.env(pin=True)
    else:
        current = (overlay / "Rules.olean").exists()
        env = lean.env(overlay, pin=True)
    with tempfile.TemporaryDirectory() as temporary:
        asked, answers = ask(
            {"mode": "rules", "rules": [r.name for r in rules]}, "import Lean\n", env, Path(temporary)
        )
    replay = run(lean.checker("Rules"), env)
    by_name = {a.get("rule"): a for a in answers if isinstance(a, dict)}
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
        }
        decision = core.decide(
            core.Verdict.PROVED,
            core.Evidence(
                lean=core.Step.of("rules_check.lean", asked),
                replay=core.Step.of("leanchecker", replay),
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
        out.append(entry)
    return {"schema": schemas.RULES_PROVED, "rules": out}


def proved_rules() -> tuple[list[lang.Rule], dict[str, Any]]:
    """The rules a search may apply: the proved ones. And the record that says so."""
    rules = gen.load_all()
    record = check(rules)
    good = {e["name"] for e in record["rules"] if e["proved"]}
    return [r for r in rules if r.name in good], record
