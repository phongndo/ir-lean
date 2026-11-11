"""Certify mode: Lean proves a chain of rule applications again.

What's certified is IR and the names of rules, and nothing a matcher says: a module whose functions `@s0` to
`@sk` are the states of a chain, each one block of integer instructions, and the rule applied at each step.
`build/ir-lean` translates the module, a certificate is generated, with a theorem for each step and `cert :
IRLean.Refines Chain.s0 Chain.sk` from them by `IRLean.Refines.trans`, and the gate decides:

1. `opt -passes=verify` accepts the module, and ir-lean translates every state, as one block without memory;
2. Lean elaborates the certificate;
3. `tools/rules/rules_check.lean` builds the claim from the two names and finds the theorem's type is that
   expression, and reads the axioms it rests on and the rules its proof uses;
4. `tests/check_axioms.lean` audits the certificate's module and everything it imports;
5. `leanchecker` replays the certificate, the generated module and every module they import but Lean's own;
6. nothing they read changed from before the certificate compiled to after the last of them ended: the
   modules, copied before any of the libraries' code ran, the toolchain, every Lean process run from it by
   path with LEAN_SYSROOT naming it, the two checkers, and the IR, the generated module, the certificate and
   the checker's own files, written in a private directory, each by its hash and `lstat` when it was written.
   The output directory gets copies, which nothing reads back. Lean runs the certificate's code, and its
   imports', as it compiles it, in a scope that kills whatever it started when it ends, where systemd can
   make one: the record says whether it did, `contained`;
7. `irlean.verdict` grants `certified`, or doesn't. `refused` is only for what a check diagnosed, and a tool
   that failed, or a file that changed, is an `error`, or `unknown` at a limit.

The record's `files` are those first hashes, so it names what was translated and checked.

A step's proof is one term, written here from the two states as the IR has them: `Rules.Mono.<instruction>`
down to where they differ, `Refine.refl_val _` for what's the same, and the rule's theorem at the instruction
that changed, every operand, flag and constant left for Lean to read off the two functions. Nothing in it is
trusted, and nothing in it searches: a matcher that applied a rule where its pattern doesn't match, or built
another replacement, gives states the rule's theorem doesn't relate, and a term that doesn't elaborate.
docs/rules.md.
"""

from __future__ import annotations

import json
import re
import shutil
import signal
import sys
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import ir
import lang
import proved

ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.append(str(ROOT / "tools"))

from irlean import hashing, lean, proc, schemas  # noqa: E402
from irlean import verdict as core  # noqa: E402

TOOL = ROOT / "build" / "ir-lean"
NAMESPACE = "Chain"
CERT = "ChainCert"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
# A step's proof follows the state as a tree. Past this many nodes it isn't written.
MAX_PROOF_NODES = 4000
TRIPLE = 'target triple = "x86_64-unknown-linux-gnu"\n'
# The checks whose failure is a diagnosis of the certificate, from the checker's answer. Any other failing
# is a tool's.
AXIOMS_CHECK = "its axioms are the standard three, or those and bv_decide's"
RULES_CHECK = "its proof uses the chain's rules, and no others"
# What tests/check_axioms.lean says when its policy refuses what a proof rests on, as tests/proofs.sh reads
# it.
POLICY = re.compile(r"not an allowed axiom|not what bv_decide would add|uses (?:implemented_by|extern)")
# What leanchecker says when the kernel rejects a declaration it replays, or a constructor or recursor isn't
# the one the kernel makes, as Lean.Replay throws them.
KERNEL = re.compile(r"^\(kernel\) |^uncaught exception: (?:Invalid|No such) (?:constructor|recursor) ")
# Lean failing to read a module a file imports: a file that isn't there, which refuses nothing.
UNREAD = re.compile(r"object file .* does not exist|unknown module prefix")


@dataclass(frozen=True)
class Step:
    """One application: the rule, the instruction it matched, and what it put there."""

    rule: lang.Rule
    old: ir.Term
    new: ir.Term


class Uncertifiable(Exception):
    """A chain no certificate is written for, and why."""


def states(root: ir.Term, steps: list[Step]) -> list[ir.Term]:
    """The chain's states, from `root`: each step replaces its instruction wherever it is."""
    out = [root]
    for step in steps:
        following = ir.replace(out[-1], step.old, step.new)
        if following == out[-1]:
            raise Uncertifiable(f"{step.rule.name} changes nothing")
        out.append(following)
    return out


# ------------------------------------------------------------------------------------------------------------
# A step's proof


def sites(s: ir.Term, t: ir.Term) -> list[tuple[ir.Term, ir.Term]]:
    """Where a rule could have been applied to turn `s` into `t`: each pair of an instruction of `s` and
    what's in its place in `t`, such that `t` is `s` with the one replaced by the other, the smallest
    first."""
    path = []
    a, b = s, t
    while True:
        path.append((a, b))
        if a[0] != "op" or b[0] != "op" or a[:4] != b[:4] or len(a[4]) != len(b[4]):
            break
        differ = {(x, y) for x, y in zip(a[4], b[4], strict=True) if x != y}
        if len(differ) != 1:
            break
        ((a, b),) = differ
    return [(old, new) for old, new in reversed(path) if old != new and ir.replace(s, old, new) == t]


def proof(s: ir.Term, t: ir.Term, old: ir.Term, new: ir.Term, rule: lang.Rule, budget: list[int]) -> Any:
    """Why `t` refines `s`, if `rule` turns `old` into `new`: a tree of a lemma's name and what it's applied
    to."""
    budget[0] -= 1
    if budget[0] < 0:
        raise Uncertifiable(f"the proof would take more than {MAX_PROOF_NODES} steps")
    if s == t:
        return "(Refine.refl_val _)"
    if s == old and t == new:
        return f"(Rules.val ({rule.instance()}))"
    if s[0] != "op" or t[0] != "op" or s[:4] != t[:4] or len(s[4]) != len(t[4]):
        raise Uncertifiable("the two states differ somewhere the rule wasn't applied")
    args = [proof(a, b, old, new, rule, budget) for a, b in zip(s[4], t[4], strict=True)]
    return (lang.OPS[s[1]].mono, args)


def render(tree: Any, indent: int) -> list[str]:
    """A proof tree as lines of at most 118 columns."""
    if isinstance(tree, str):
        return [" " * indent + tree]

    def flat(node: Any) -> str:
        return node if isinstance(node, str) else "(" + " ".join([node[0], *(flat(a) for a in node[1])]) + ")"

    one = flat(tree)
    if indent + len(one) <= 118:
        return [" " * indent + one]
    lines = [" " * indent + "(" + tree[0]]
    for arg in tree[1]:
        lines += render(arg, indent + 2)
    lines[-1] += ")"
    return lines


def certificate(
    lean_names: list[str], rules: list[lang.Rule], terms: list[ir.Term], params: int, noundef: int
) -> str:
    """The certificate: a theorem for each step, and `cert` from them."""
    out = [
        f"import Rules\nimport {NAMESPACE}\n\n"
        "/-! A chain of rule applications, certified. Written by `tools/rules/rules.py`: each step's\n"
        "proof is the rule's theorem at the instruction that changed, carried to the function's result\n"
        "by congruence, and `cert` is the steps composed by `IRLean.Refines.trans`. docs/rules.md says\n"
        "what it claims. -/\n\n"
        "open IRLean\n"
    ]
    names = " ".join(f"a{i}" for i in range(params))
    for i, rule in enumerate(rules):
        places = sites(terms[i], terms[i + 1])
        if not places:
            raise Uncertifiable(f"step {i} changes nothing")
        trees = [proof(terms[i], terms[i + 1], old, new, rule, [MAX_PROOF_NODES]) for old, new in places]
        src, tgt = f"{NAMESPACE}.{lean_names[i]}", f"{NAMESPACE}.{lean_names[i + 1]}"
        out.append(f"\n/-- `{rule.name}`: {lang.show(rule.pattern)} to {lang.show(rule.replacement)}. -/\n")
        out.append(f"theorem Cert.step_{i} : IRLean.Refines {src} {tgt} := by\n")
        if params:
            out.append(f"  intro {names}\n")
        hole = "?_"
        for _ in range(noundef):
            hole = f"(Rules.noundef_mono {hole})"
        if noundef:
            out.append(f"  refine {hole[1:-1]}\n")
        out.append("  refine Rules.le_of_ret (by rfl) (by rfl) ?_\n")
        if len(trees) == 1:
            out.append("  exact\n" + "\n".join(render(trees[0], 4)) + "\n")
        else:
            # The states don't say which of these instructions the rule was applied at: the first that fits.
            out.append("  first\n")
            for tree in trees:
                out.append("  | exact\n" + "\n".join(render(tree, 6)) + "\n")
    whole = "Cert.step_0"
    for i in range(1, len(rules)):
        whole = (
            f"IRLean.Refines.trans ({whole}) Cert.step_{i}"
            if i > 1
            else f"IRLean.Refines.trans {whole} Cert.step_{i}"
        )
    first, last = f"{NAMESPACE}.{lean_names[0]}", f"{NAMESPACE}.{lean_names[-1]}"
    out.append(f"\ntheorem Cert.cert : IRLean.Refines {first} {last} :=\n  {whole}\n")
    return "".join(out)


def function_term(f: ir.Function) -> ir.Term:
    """What a function of one block returns, as a term of its arguments."""
    returned = ir.one_block(f)
    if returned is None:
        raise Uncertifiable(f"@{f.name} isn't one block of integer instructions the certifier follows")
    token, width = returned
    return ir.term(f, token, width, ir.members(f, token, None))


# ------------------------------------------------------------------------------------------------------------
# The gate

DEF = (
    r"^noncomputable def {name}(?P<params>(?: \(\S+ : Val \d+\))*) : Outcome \(Val \d+\) :=\n"
    r"(?P<body>(?:  .*\n)+)"
)


def shape(generated: str, name: str) -> tuple[int, int] | None:
    """How many arguments the generated function takes, and how many are `noundef`, if it's one block run
    after nothing but `noundef` checks. None if it's any other shape."""
    m = re.search(DEF.format(name=re.escape(name)), generated, re.M)
    if not m:
        return None
    lines = m["body"].splitlines()
    if not re.fullmatch(rf"  run \({re.escape(name)}\.step\) \(\.\S+( \S+)*\)", lines[-1]):
        return None
    if any(not re.fullmatch(r"  noundef \S+ <\|", line) for line in lines[:-1]):
        return None
    return m["params"].count("("), len(lines) - 1


def check(
    module: str,
    rules: list[lang.Rule],
    out: Path,
    scope: str,
    proof_text: str | None = None,
    overlay: Path | None = None,
) -> dict[str, Any]:
    """Runs the gate on a chain: `module`'s functions `@s0` to `@sk` are its states, and `rules[i]` is the
    rule applied from `@s<i>` to the next. Works in a private directory, writes copies of what it checked
    and the verdict to `out`, and returns the verdict, schema RULES_CERTIFICATE.
    For tests: `proof_text` replaces the certificate this would write, and `overlay` is a directory holding
    another build of the `Rules` library, read in place of the repo's."""
    with tempfile.TemporaryDirectory(prefix="ir-lean-certify-") as modules:
        return gate(module, rules, out, scope, proof_text, overlay, Path(modules))


def gate(
    module: str,
    rules: list[lang.Rule],
    out: Path,
    scope: str,
    proof_text: str | None,
    overlay: Path | None,
    modules: Path,
) -> dict[str, Any]:
    """`check`, with `modules`, a private directory: for the copies the checks read, and `work`, where the IR
    is written, translated, and the certificate written and compiled. Nothing outside the process knows it, so
    an editor or another build writing into `out` changes nothing the verdict is about. `out` gets copies, of
    the IR, the generated module and the certificate as they were bound, and the verdict, which nothing
    reads back."""
    started = time.monotonic()
    out = out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    for stale in out.glob("*.olean"):
        stale.unlink()
    work = modules / "work"
    work.mkdir()
    names = [f"s{i}" for i in range(len(rules) + 1)]
    record: dict[str, Any] = {
        "schema": schemas.RULES_CERTIFICATE,
        "status": "error",
        "reason": "",
        "detail": "",
        "claim": {"src": names[0], "tgt": names[-1], "statement": None},
        "tier": {"scope": scope, "axioms": None},
        "chain": [
            {"rule": r.name, "match": lang.show(r.pattern), "replace": lang.show(r.replacement)}
            for r in rules
        ],
        "rules_used": [],
        "axioms": [],
        "files": {},
        "checks": {},
        "contained": None,
    }
    checks: dict[str, bool | None] = {}
    record["checks"] = checks
    # The IR, the generated module and the certificate in `work`, each by its hash when it was written, before
    # anything read it: what the record names, and what each has to still be when the verdict is given. And
    # each by `lstat` then, so a write that was put back shows too. `published` is their bytes, for `out`.
    written: dict[str, str] = record["files"]
    stamped: dict[str, dict[str, tuple[int, ...]]] = {}
    published: dict[str, bytes] = {}

    def bind(name: str, data: bytes) -> None:
        """Holds `work / name`, which is `data`, as `written`, `stamped` and `published` say."""
        stamped[name] = hashing.stamp(work / name)
        written[name] = hashing.sha256(data)
        published[name] = data

    def differ() -> list[str]:
        """Each file of `written` that isn't, now, what it was when it was written, by hash or by `lstat`."""
        return [
            str(work / name)
            for name, digest in written.items()
            if not (work / name).is_file()
            or hashing.stamp(work / name) != stamped[name]
            or hashing.sha256_file(work / name) != digest
        ]

    def done(status: str, reason: str, detail: str = "") -> dict[str, Any]:
        record.update(
            status=status, reason=reason, detail=detail[:2000], seconds=round(time.monotonic() - started, 2)
        )
        for name, data in published.items():
            (out / name).write_bytes(data)
        schemas.write(out / "verdict.json", record, schemas.RULES_CERTIFICATE, indent=1, ensure_ascii=False)
        return record

    (work / "chain.ll").write_bytes(module.encode())
    bind("chain.ll", module.encode())
    verified = proved.run(["opt", "-passes=verify", "-disable-output", "chain.ll"], cwd=work)
    checks["opt verifies each state"] = verified.exit == 0
    if verified.exit != 0:
        return done("error", "ir_invalid", verified.output)
    reported = proved.run([str(TOOL), "chain.ll", "--report"], cwd=work)
    rows = {r[1]: r for r in (line.split("\t") for line in reported.out.splitlines()) if len(r) >= 7}
    lean_names = []
    for name in names:
        row = rows.get(name)
        if row is None or row[0] != "ok" or row[-1] != "pure" or row[4] != "1":
            checks["ir-lean translates each state, as one block without memory"] = False
            return done("unsupported", "state_unsupported", f"{name}: {(row or ['not translated'])[-1]}")
        lean_names.append(row[2])
    checks["ir-lean translates each state, as one block without memory"] = True
    generated = work / f"{NAMESPACE}.lean"
    emitted = proved.run(
        [str(TOOL), "chain.ll", "--no-code", "--namespace", NAMESPACE, "-o", generated.name], cwd=work
    )
    if emitted.exit != 0 or not generated.is_file():
        return done("error", "tool_failed", emitted.output)
    emitted_text = generated.read_bytes()
    bind(generated.name, emitted_text)
    shapes = [shape(emitted_text.decode(), name) for name in lean_names]
    if any(s is None for s in shapes) or len(set(shapes)) != 1:
        return done("unsupported", "shape_unsupported", "a state isn't one block run after `noundef` checks")
    assert shapes[0] is not None
    params, noundef = shapes[0]
    try:
        by_name = {f.name: f for f in ir.functions(module)}
        terms = [function_term(by_name[name]) for name in names]
        text = (
            proof_text if proof_text is not None else certificate(lean_names, rules, terms, params, noundef)
        )
    except (Uncertifiable, ir.IRError) as error:
        return done("unsupported", "proof_not_written", str(error))
    (work / f"{CERT}.lean").write_bytes(text.encode())
    bind(f"{CERT}.lean", text.encode())

    # Lean runs the certificate's code as it compiles it, and the code of what it imports, the Rules library's
    # and Peephole's. Everything a check reads is held from before then to after the last check, against that
    # code and anything else running, such as another build in the checkout: the libraries, copied into `lib`
    # first, the toolchain and the two checkers. The generated module, compiled first, is held by its hash,
    # and the checks read it and the certificate from copies in `own`, so nothing the compile left in `work`
    # can stand in for them. docs/rules.md's "What the gates promise" says what this holds against.
    lib = proved.copy_libraries(modules / "lib", overlay)
    prefix = proved.toolchain()
    trusted = (lib, prefix, proved.CHECK, lean.AXIOM_AUDIT)
    sealed = proved.seal(*trusted)
    env = proved.lean_env(prefix, work, lib)
    compiled = proved.run(
        lean.argv(
            proved.LEAN_MB, "-o", f"{NAMESPACE}.olean", generated.name, lean=proved.binary(env, "lean")
        ),
        env,
        cwd=work,
    )
    if compiled.exit != 0:
        return done("error", "generated_module_failed", compiled.output)
    generated_sha256 = hashing.sha256_file(work / f"{NAMESPACE}.olean")
    # In a scope, so whatever the certificate's code started is killed when Lean ends, in whatever session.
    # Where systemd can't make one, a process it started in a session of its own can outlive it unseen.
    cert = proved.run(
        lean.argv(proved.LEAN_MB, "-o", f"{CERT}.olean", f"{CERT}.lean", lean=proved.binary(env, "lean")),
        env,
        cwd=work,
        scope=proc.Scope("ir-lean-certify", proved.LEAN_MB + 512),
    )
    record["contained"] = cert.unit is not None
    cert_step = core.Step.of("lean", cert)
    own = modules / "own"
    own.mkdir()
    for name in (NAMESPACE, CERT):
        if (work / f"{name}.olean").is_file():
            shutil.copyfile(work / f"{name}.olean", own / f"{name}.olean")
    moved = proved.unsealed(sealed, *trusted) + differ()
    copied = own / f"{NAMESPACE}.olean"
    if not copied.is_file() or hashing.sha256_file(copied) != generated_sha256:
        moved.append(f"{work / NAMESPACE}.olean")
    if moved:
        return done(
            "error",
            "artifacts_modified",
            "changed by the time the certificate compiled:\n" + "\n".join(moved),
        )
    if cert.exit != 0 or cert.limit is not None:
        return done(*failed(cert))
    bound = proved.seal(own)
    env = proved.lean_env(prefix, own, lib)
    asked, answers, asked_moved = proved.ask(
        {
            "mode": "cert",
            "src": f"{NAMESPACE}.{lean_names[0]}",
            "tgt": f"{NAMESPACE}.{lean_names[-1]}",
            "generated_module": NAMESPACE,
            "certificate_module": CERT,
            "theorem": "Cert.cert",
            "run_dir": str(own.resolve()),
            "library_dirs": [str(lib.resolve())],
        },
        f"import IRLean\nimport {NAMESPACE}\n",
        env,
        work,
    )
    if asked_moved:
        return done(
            "error", "artifacts_modified", "changed while the checker ran:\n" + "\n".join(asked_moved)
        )
    # What a checker answered counts only if it then ended cleanly: one that crashed or was stopped after
    # answering says nothing it can be held to.
    checks["rules_check.lean ended on its own, with 0"] = asked.exit == 0 and asked.limit is None
    if not checks["rules_check.lean ended on its own, with 0"]:
        return done(*failed(asked, None))
    answer = answers[0] if len(answers) == 1 and isinstance(answers[0], dict) else {}
    checks["the theorem states that the last state refines the first"] = answer.get("ok") is True
    if answer.get("ok") is not True:
        if answer.get("reason") in (None, "checker_error"):
            return done("error", "tool_failed", json.dumps(answer, ensure_ascii=False) + "\n" + asked.output)
        return done("refused", str(answer["reason"]), json.dumps(answer, ensure_ascii=False))
    record["claim"]["statement"] = answer["statement"]
    record["rules_used"], record["axioms"] = answer["rules"], answer["axioms"]
    others = [a for a in answer["axioms"] if a not in STANDARD]
    solver = [a for a in others if re.search(r"\._native\.bv_decide\.ax_", a)]
    record["tier"]["axioms"] = "standard" if not others else "bv_decide" if solver == others else None
    checks[AXIOMS_CHECK] = record["tier"]["axioms"] is not None
    wanted = sorted({r.name for r in rules})
    checks[RULES_CHECK] = answer["rules"] == wanted
    listed = answer.get("replay")
    checks["leanchecker replays the certificate and the generated module, and what they import"] = isinstance(
        listed, list
    ) and {NAMESPACE, CERT} <= {m for m in listed if isinstance(m, str)}
    audit = proved.run(
        lean.audit_argv(proved.LEAN_MB, lean=proved.binary(env, "lean")),
        lean.audit_env(CERT, base=env),
        cwd=work,
    )
    replay = proved.replay(listed, env, cwd=work)
    moved = proved.unsealed(sealed, *trusted) + proved.unsealed(bound, own) + differ()
    checks[proved.UNCHANGED] = not moved
    if moved:
        return done("error", "artifacts_modified", "changed while they were checked:\n" + "\n".join(moved))
    files = {name: (work / name).exists() for name in ("chain.ll", f"{NAMESPACE}.lean", f"{CERT}.lean")}
    return done(*conclude(cert_step, core.Step.of("check_axioms", audit), replay, files, checks))


def conclude(
    cert: core.Step,
    audit: core.Step,
    replay: core.Step,
    files: dict[str, bool],
    checks: dict[str, bool | None],
) -> tuple[str, str, str]:
    """The status, reason and detail of a certificate's evidence: `certified` only if irlean.verdict grants
    it. A limit is `unknown`. `refused` is only for a diagnosis: the checker's answer that the theorem rests
    on an axiom that isn't allowed or uses other rules than the chain's, tests/check_axioms.lean's policy
    refusing it, or the kernel rejecting a declaration leanchecker replays. Anything else, such as a crash, a
    missing file, or a process that failed without saying why, is an `error`: a tool that failed decided
    nothing."""
    decision = core.decide(
        core.Verdict.CERTIFIED,
        core.Evidence(lean=cert, replay=replay, axioms=audit, files=files, checks=checks),
    )
    if decision.granted:
        return "certified", decision.reason, decision.detail
    if decision.verdict is core.Verdict.UNKNOWN:
        return "unknown", decision.reason, decision.detail
    unmet = {name for name, passed in checks.items() if passed is not True}
    if decision.reason == "check_failed" and unmet <= {AXIOMS_CHECK, RULES_CHECK}:
        return "refused", decision.reason, decision.detail
    if decision.reason == "no_evidence":
        for step, reason, said in (
            (audit, "disallowed_axiom", POLICY),
            (replay, "kernel_replay_failed", KERNEL),
        ):
            if step.exit != 0 or step.limit is not None:
                return failed(step, reason, said)
    return "error", decision.reason, decision.detail


def failed(
    ran: proc.Ran | core.Step, reason: str | None = "proof_failed", said: re.Pattern[str] | None = None
) -> tuple[str, str, str]:
    """The status, reason and detail of a process that didn't end on its own with 0: by default, Lean
    compiling a certificate. A limit is `unknown`, and SIGKILL is how a cap or the OOM killer stops a process.
    A signal or a crash is no answer, so it's an `error`, even after the process printed an error: what it
    printed may be a part. Otherwise an error the process reported and exited on, a Lean error or a line
    `said` matches, is `refused` for `reason`, but not empty output, and not an error about a module it
    couldn't read, which is a file that isn't there. With `reason` None, as for a checker, whose refusals
    are answers, nothing is a refusal."""
    limit = ran.limit or lean.limit_of(ran.output)
    if limit is None and ran.exit in (-signal.SIGKILL, 128 + signal.SIGKILL):
        limit = "killed"
    if limit:
        return "unknown", str(limit), ran.output
    if reason is not None and ran.exit is not None and 0 < ran.exit < 128:
        if said is None:
            errors = [m.text for m in lean.messages(ran.output) if m.severity == "error"]
        else:
            errors = [line for line in ran.output.splitlines() if said.search(line)]
        if errors and not any(UNREAD.search(e) for e in errors):
            return "refused", reason, "\n".join(errors)
    return "error", "tool_failed", f"ended with {ran.exit}\n{ran.output}"


def chain_module(preamble: str, texts: list[tuple[str, list[str]]]) -> str:
    """One module of a chain's states, each a function's text and the declarations it needs."""
    declares = sorted({d for _, needs in texts for d in needs})
    return (
        (preamble or TRIPLE)
        + "\n"
        + "".join(f"{d}\n" for d in declares)
        + "\n"
        + "\n".join(t for t, _ in texts)
    )
