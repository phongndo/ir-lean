#!/usr/bin/env python3
"""Checks the model of LLVM's `simplifyAddInst` in tests/cpp_correspondence against the pinned C++ and opt.

The model is a manual translation of the C++, and its theorem says each value it returns refines the `add` at
every width. What ties the model to the C++ is checked here, and none of it is a proof:

- anchors: llvm-project is the pinned one, by NAR hash, and every line `anchors.json` quotes is at that line
of a file with that SHA-256. Every code line of the three functions modelled is quoted by some anchor, every
`[cpp:<id>]` tag in the Lean and docs/llvm-cpp-correspondence.md has an anchor, and every anchor is cited. A
changed line and a missing anchor are each refused.
- lean: the model and its theorem compile with warnings as errors, rest on the standard axioms only, and
`leanchecker` replays them.
- differential: the model's answer for each generated `add` is what the pinned `opt -passes=instsimplify`
makes of it. Cases where the model calls code it doesn't model aren't compared. Cases where InstSimplify
changes an operand before it reaches the `add` are left out, since `simplifyAddInst` would see other
operands. Every named case below has to be compared, or checked as delegated.
- mutants: dropping the `nuw` guard of `add nuw x, -1` breaks the theorem and the comparison. Dropping the
flag guard of the sign-mask rule keeps the theorem, since that rewrite is right without flags, and only the
comparison with `opt` finds it.

One process at a time, each with a time limit and Lean's memory limit, in a systemd scope capped at 512 MB
more with no swap where one can be made. A limit is reported as UNKNOWN and fails the run: it's never a pass.
Needs `nix develop`, for `LLVM_PROJECT_SRC`, `opt`, `nix` and `lean`. Writes only to a temporary directory.

usage: tests/cpp_correspondence.py [--timeout SECONDS] [--memory MB] [--keep]
"""

import argparse
import contextlib
import hashlib
import json
import os
import re
import secrets
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
HERE = ROOT / "tests" / "cpp_correspondence"
LEAN_FILES = ["SimplifyAddModel.lean", "SimplifyAddSound.lean"]
DOC = ROOT / "docs" / "llvm-cpp-correspondence.md"
LIMIT = re.compile(
    r"maximum number of heartbeats|\(deterministic\) timeout|maximum recursion depth|deep recursion|"
    r"stack overflow|excessive memory|out of memory|maximum number of steps"
)
TAG = re.compile(r"\[cpp:([A-Za-z][A-Za-z0-9_.]*)\]")


class Unknown(Exception):
    """A time or memory limit stopped a step, so its result is unknown."""


class Runner:
    def __init__(self, timeout: int, memory_mb: int) -> None:
        self.timeout, self.memory_mb = timeout, memory_mb
        probe = ["systemd-run", "--user", "--scope", "--quiet", "--", "true"]
        self.capped = bool(shutil.which("systemd-run")) and (
            subprocess.run(probe, capture_output=True, check=False).returncode == 0
        )
        self.env = {**os.environ, "ELAN_TOOLCHAIN": (ROOT / "lean-toolchain").read_text().strip()}

    def __call__(self, argv: list[str], env: dict[str, str] | None = None) -> subprocess.CompletedProcess:
        unit = f"ir-lean-correspondence-{os.getpid()}-{secrets.token_hex(4)}"
        command = argv
        if self.capped:
            command = [
                "systemd-run",
                "--user",
                "--scope",
                "--quiet",
                f"--unit={unit}",
                f"--property=MemoryMax={self.memory_mb + 512}M",
                "--property=MemorySwapMax=0",
                "--",
                *argv,
            ]
        with tempfile.TemporaryFile() as out, tempfile.TemporaryFile() as err:
            p = subprocess.Popen(
                command,
                stdin=subprocess.DEVNULL,
                stdout=out,
                stderr=err,
                env={**self.env, **(env or {})},
                start_new_session=True,
            )
            try:
                p.wait(timeout=self.timeout)
            except subprocess.TimeoutExpired as e:
                raise Unknown(f"{Path(argv[0]).name} took more than {self.timeout} s") from e
            finally:
                # Whatever it left running goes too.
                if self.capped:
                    subprocess.run(
                        ["systemctl", "--user", "kill", "--signal=SIGKILL", f"{unit}.scope"],
                        capture_output=True,
                        check=False,
                    )
                with contextlib.suppress(ProcessLookupError, PermissionError):
                    os.killpg(p.pid, signal.SIGKILL)
                p.wait()
            out.seek(0)
            err.seek(0)
            r = subprocess.CompletedProcess(argv, p.returncode, out.read().decode(), err.read().decode())
        said = r.stdout + r.stderr
        if r.returncode < 0 or r.returncode == 137 or (r.returncode != 0 and LIMIT.search(said)):
            raise Unknown(f"{Path(argv[0]).name} hit a limit: {said[-400:]}")
        return r

    def lean(self, *args: str) -> list[str]:
        return ["lean", "-j1", "-M", str(self.memory_mb), *args]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


# ### Anchors


def check_anchors(src: Path, anchors: dict, cited: str) -> list[str]:
    """What's wrong with `anchors` against the source tree `src`, and the Lean and doc text `cited`."""
    problems = []
    for name, digest in anchors["files"].items():
        if not (src / name).is_file() or sha256(src / name) != digest:
            problems.append(f"{name} isn't the file recorded")
    lines = {
        name: (src / name).read_text().split("\n") for name in anchors["files"] if (src / name).is_file()
    }
    quoted: dict[str, set[int]] = {}
    for a in anchors["anchors"]:
        text = lines.get(a["file"], [])
        got = [line for s, e in a["ranges"] for line in text[s - 1 : e]]
        if got != a["text"]:
            problems.append(f"anchor {a['id']}: {a['file']} doesn't say this at {a['ranges']}")
        quoted.setdefault(a["file"], set()).update(n for s, e in a["ranges"] for n in range(s, e + 1))
    for c in anchors["covered"]:
        s, e = c["range"]
        for n in range(s, e + 1):
            line = lines.get(c["file"], [""] * e)[n - 1].strip()
            if line and not line.startswith("//") and n not in quoted.get(c["file"], set()):
                problems.append(f"{c['function']}: {c['file']}:{n} is code no anchor quotes: {line}")
    ids = {a["id"] for a in anchors["anchors"]}
    tags = set(TAG.findall(cited))
    problems += [f"[cpp:{t}] has no anchor" for t in sorted(tags - ids)]
    problems += [f"anchor {i} isn't cited" for i in sorted(ids - tags)]
    return problems


def check_pin(run: Runner, anchors: dict, src: Path) -> list[str]:
    """The source, `opt` and the inventory are the repo's pinned LLVM."""
    problems = []
    pin = tomllib.loads((ROOT / "tests" / "llvm" / "targets.toml").read_text())["project"]
    if anchors["llvm"] != pin:
        problems.append(f"anchors.json names {anchors['llvm']}, but tests/llvm/targets.toml pins {pin}")
    nar = run(["nix", "hash", "path", str(src)])
    if nar.returncode != 0 or nar.stdout.strip() != pin["nix_hash"]:
        problems.append(f"LLVM_PROJECT_SRC has NAR hash {nar.stdout.strip()}, not {pin['nix_hash']}")
    version = pin["tag"].removeprefix("llvmorg-")
    opt = run(["opt", "--version"])
    if f"LLVM version {version}\n" not in opt.stdout:
        problems.append(f"opt isn't LLVM {version}: {opt.stdout.strip()}")
    inventory = json.loads((ROOT / "tests" / "llvm_scope" / "inventory.json").read_text())
    item = next(i for i in inventory["items"] if i["id"] == "pass:instsimplify")
    for name, digest in item["anchors"].items():
        if anchors["files"].get(name) != digest:
            problems.append(f"the inventory's pass:instsimplify has {name} at {digest}, anchors.json doesn't")
    return problems


# ### Cases

A0, A1 = ("arg", 0), ("arg", 1)


def signed(v: int, w: int) -> int:
    v %= 1 << w
    return v - (1 << w) if v >> (w - 1) else v


class Ids:
    def __init__(self) -> None:
        self.n = 10

    def __call__(self) -> int:
        self.n += 1
        return self.n


def sub(ids: Ids, a: tuple, b: tuple, nuw: bool = False, nsw: bool = False) -> tuple:
    return ("sub", ids(), nuw, nsw, a, b)


def xor(ids: Ids, a: tuple, b: tuple) -> tuple:
    return ("xor", ids(), a, b)


def const(c: int) -> tuple:
    return ("const", c)


def bases(w: int, ids: Ids) -> list[tuple]:
    sm, ones = signed(1 << (w - 1), w), -1
    out: list[tuple] = [A0, A1, ("poison",), ("undef",)]
    out += [const(c) for c in dict.fromkeys(signed(c, w) for c in (0, 1, -1, 1 << (w - 1)))]
    out += [
        sub(ids, A0, A1),
        sub(ids, A0, A1, nsw=True),
        xor(ids, A0, A1),
        ("add", ids(), False, False, A0, A1),
    ]
    out += [
        xor(ids, A0, const(ones)),
        xor(ids, const(ones), A0),
        xor(ids, A0, const(sm)),
        xor(ids, const(sm), A0),
    ]
    if w > 1:
        out += [sub(ids, const(0), A0), sub(ids, const(0), A0, nsw=True)]
    return out


def derived(w: int, p: tuple, ids: Ids) -> list[tuple]:
    """Operands that the rules look for next to `p`: `Y - p`, `0 - p`, `~p`, `b - a` for `p = a - b`, and an
    instruction like `p` that isn't `p`, alone and as `a1 - copy`."""
    out = [sub(ids, y, p) for y in (A0, A1) if y != p]
    if w > 1:
        out += [sub(ids, const(0), p), sub(ids, const(0), p, nsw=True)]
    out += [xor(ids, p, const(-1)), xor(ids, const(-1), p)]
    if p[0] == "sub":
        out += [sub(ids, p[5], p[4]), sub(ids, p[5], p[4], nuw=True, nsw=True)]
    if p[0] in ("sub", "xor", "add"):
        copy = (p[0], ids(), *p[2:])
        out += [copy, sub(ids, A1, copy)]
    return out


def sentinels(ids: Ids) -> list[tuple[str, int, tuple, tuple, bool, bool, str]]:
    """Named cases, one or more for each step of the model, with what the model and `opt` should both give:
    an IR value, `%r` where the `add` stays, or `delegated` where nothing's compared."""
    s01 = sub(ids, A0, A1)
    s10 = sub(ids, A1, A0)
    sm = -128
    return [
        ("add.poison", 8, A0, ("poison",), False, False, "poison"),
        ("add.undef", 8, A0, ("undef",), False, False, "undef"),
        ("add.zero", 8, A0, const(0), True, True, "%a0"),
        ("fold.swap", 8, const(0), A0, False, False, "%a0"),
        ("fold.both", 8, const(1), const(2), False, False, "delegated"),
        ("negation.of_op1", 8, sub(ids, const(0), A1), A1, False, False, "0"),
        ("negation.of_op0", 8, A0, sub(ids, const(0), A0, nsw=True), True, False, "0"),
        ("negation.swapped", 8, s01, s10, False, False, "0"),
        ("subCancel.op1", 8, A0, s10, False, False, "%a1"),
        ("subCancel.op0", 8, s10, A0, False, True, "%a1"),
        ("subCancel.same_pointer", 8, s01, sub(ids, A1, s01), False, False, "%a1"),
        ("subCancel.other_pointer", 8, s01, sub(ids, A1, sub(ids, A0, A1)), False, False, "%r"),
        ("not.op0", 8, xor(ids, A0, const(-1)), A0, False, False, "-1"),
        ("not.op0_commuted", 8, xor(ids, const(-1), A0), A0, False, False, "-1"),
        ("not.op1", 8, A0, xor(ids, const(-1), A0), True, True, "-1"),
        ("signMask.nsw", 8, xor(ids, A0, const(sm)), const(sm), True, False, "%a0"),
        ("signMask.nuw", 8, xor(ids, A0, const(sm)), const(sm), False, True, "%a0"),
        ("signMask.no_flags", 8, xor(ids, A0, const(sm)), const(sm), False, False, "%r"),
        ("signMask.commuted_xor", 8, xor(ids, const(sm), A0), const(sm), True, False, "%r"),
        ("nuwAllOnes", 8, A0, const(-1), False, True, "-1"),
        ("allOnes.no_nuw", 8, A0, const(-1), True, False, "%r"),
        ("i1", 1, A0, A1, False, False, "delegated"),
        ("i1.zero", 1, A0, const(0), False, False, "%a0"),
        ("assoc", 8, ("add", ids(), False, False, A0, A1), A1, False, False, "delegated"),
        ("null", 32, A0, A1, True, True, "%r"),
    ]


def cases() -> list[dict]:
    ids = Ids()
    out = []
    for name, w, op0, op1, nsw, nuw, expect in sentinels(ids):
        out.append({"name": name, "w": w, "op0": op0, "op1": op1, "nsw": nsw, "nuw": nuw, "expect": expect})
    flags = [(False, False), (True, False), (False, True), (True, True)]
    for w in (1, 8, 32):
        base = bases(w, ids)
        pairs = [(a, b) for a in base for b in base]
        for p in base:
            if p[0] in ("arg", "sub", "xor", "add"):
                for d in derived(w, p, ids):
                    pairs += [(p, d), (d, p)]
        for i, (op0, op1) in enumerate(pairs):
            for nsw, nuw in flags:
                out.append(
                    {
                        "name": f"w{w}.{i}.{int(nsw)}{int(nuw)}",
                        "w": w,
                        "op0": op0,
                        "op1": op1,
                        "nsw": nsw,
                        "nuw": nuw,
                    }
                )
    return out


def operand_json(op: tuple) -> object:
    match op:
        case ("arg", i):
            return {"other": i}
        case ("const", c):
            return {"const": str(c)}
        case ("poison",) | ("undef",):
            return op[0]
        case ("sub" | "add", i, nuw, nsw, a, b):
            return {op[0]: [i, nuw, nsw, operand_json(a), operand_json(b)]}
        case ("xor", i, a, b):
            return {"xor": [i, operand_json(a), operand_json(b)]}
    raise ValueError(op)


def const_text(c: int, w: int) -> str:
    return ("true" if c % 2 else "false") if w == 1 else str(signed(c, w))


def ref(op: tuple, w: int) -> str:
    match op:
        case ("arg", i):
            return f"%a{i}"
        case ("const", c):
            return const_text(c, w)
        case ("poison",) | ("undef",):
            return op[0]
    return f"%n{op[1]}"


def emit(op: tuple, w: int, seen: dict[int, tuple], body: list[str]) -> None:
    """The instructions `op` needs, each once, operands first. One id is one instruction."""
    if op[0] not in ("sub", "xor", "add"):
        return
    if op[1] in seen:
        assert seen[op[1]] == op, f"two instructions with id {op[1]}"
        return
    seen[op[1]] = op
    a, b = op[-2], op[-1]
    emit(a, w, seen, body)
    emit(b, w, seen, body)
    flags = "".join(f for f, on in ((" nuw", op[2]), (" nsw", op[3])) if on) if op[0] != "xor" else ""
    body.append(f"  %n{op[1]} = {op[0]}{flags} i{w} {ref(a, w)}, {ref(b, w)}")


def module(all_cases: list[dict]) -> str:
    """One function a case. The call keeps both operands alive whatever happens to the `add`, so every other
    line has to come out of InstSimplify unchanged."""
    out = []
    for n, c in enumerate(all_cases):
        w, body, seen = c["w"], [], {}
        emit(c["op0"], w, seen, body)
        emit(c["op1"], w, seen, body)
        a, b = ref(c["op0"], w), ref(c["op1"], w)
        flags = "".join(f for f, on in ((" nuw", c["nuw"]), (" nsw", c["nsw"])) if on)
        out += [f"define i{w} @c{n}(i{w} %a0, i{w} %a1) {{", *body]
        out += [
            f"  call void @use{w}(i{w} {a}, i{w} {b})",
            f"  %r = add{flags} i{w} {a}, {b}",
            f"  ret i{w} %r",
            "}",
        ]
    out += [f"declare void @use{w}(i{w}, i{w})" for w in (1, 8, 32)]
    return "\n".join(out) + "\n"


def functions(ir: str) -> dict[str, list[str]]:
    out, name = {}, None
    for line in ir.split("\n"):
        if m := re.match(r"define i\d+ @(c\d+)\(", line):
            name, out[m[1]] = m[1], []
        elif line == "}":
            name = None
        elif name is not None:
            out[name].append(line)
    return out


def expected_text(result: object, c: dict) -> str | None:
    """What `ret` should name, from the model's answer, or None if it delegated."""
    if result == "null":
        return "%r"
    assert isinstance(result, dict)
    if "delegated" in result:
        return None
    ident = result["value"]
    if ident in ("poison", "undef"):
        return ident
    if "const" in ident:
        return const_text(int(ident["const"]), c["w"])
    return f"%a{ident['node']}" if ident["node"] < 10 else f"%n{ident['node']}"


def compare(all_cases: list[dict], answers: dict[str, object], before: str, after: str) -> dict:
    """Mismatches, and how many cases were compared, delegated, or left out since an operand changed first."""
    pre, post = functions(before), functions(after)
    report = {"compared": 0, "delegated": 0, "operand_changed": 0, "mismatches": [], "sentinel_problems": []}
    for n, c in enumerate(all_cases):
        fn = f"c{n}"
        keep = [x for x in pre[fn] if not x.startswith(("  %r = add", "  ret "))]
        got = [x for x in post[fn] if not x.startswith(("  %r = add", "  ret "))]
        rets = [x.split()[-1] for x in post[fn] if x.startswith("  ret ")]
        answer = answers[c["name"]]
        expect = expected_text(answer, c)
        if "expect" in c and c["expect"] != (expect or "delegated"):
            report["sentinel_problems"].append(f"{c['name']}: the model gives {answer}, not {c['expect']}")
        if keep != got:
            report["operand_changed"] += 1
            if "expect" in c:
                report["sentinel_problems"].append(f"{c['name']}: InstSimplify changed an operand first")
            continue
        if expect is None:
            report["delegated"] += 1
            continue
        report["compared"] += 1
        if rets != [expect]:
            report["mismatches"].append(f"{c['name']}: the model gives {expect}, opt gives {rets}")
    return report


# ### Lean


def build(run: Runner, work: Path, model: str, strict: bool = True) -> str | None:
    """Compiles IRLean's integer modules, `model` as the model, then the theorem, into `work`, with warnings
    as errors if `strict`. The module that failed, with Lean's errors, or None."""
    (work / "IRLean").mkdir(parents=True, exist_ok=True)
    for name in ("Attr", "Basic", "Int"):
        shutil.copy(ROOT / "IRLean" / f"{name}.lean", work / "IRLean" / f"{name}.lean")
    (work / "SimplifyAddModel.lean").write_text(model)
    for name in ("SimplifyAddSound", "Driver"):
        shutil.copy(HERE / f"{name}.lean", work / f"{name}.lean")
    steps = [("IRLean/Attr", []), ("IRLean/Basic", []), ("IRLean/Int", [])]
    strictly = ["-DwarningAsError=true"] if strict else []
    steps += [("SimplifyAddModel", strictly), ("SimplifyAddSound", strictly)]
    for path, options in steps:
        olean, source = str(work / f"{path}.olean"), str(work / f"{path}.lean")
        r = run(run.lean(*options, "-R", str(work), "-o", olean, source), {"LEAN_PATH": str(work)})
        if r.returncode != 0:
            return f"{path}: {r.stdout}{r.stderr}"
    return None


def answers(run: Runner, work: Path, all_cases: list[dict]) -> dict[str, object]:
    path = work / "cases.jsonl"
    with path.open("w") as f:
        for c in all_cases:
            j = {k: c[k] for k in ("name", "w", "nsw", "nuw")}
            j |= {"op0": operand_json(c["op0"]), "op1": operand_json(c["op1"])}
            f.write(json.dumps(j) + "\n")
    r = run(run.lean("--run", str(work / "Driver.lean"), str(path)), {"LEAN_PATH": str(work)})
    if r.returncode != 0:
        raise RuntimeError(f"the driver failed: {r.stdout[-2000:]}{r.stderr[-2000:]}")
    return {j["name"]: j["result"] for j in map(json.loads, r.stdout.splitlines())}


MUTANTS = [
    (
        "drop the nuw guard of add nuw x, -1",
        "  if isNUW && allOnes op1 then .value op1",
        "  if allOnes op1 then .value op1",
        False,
        "allOnes.no_nuw",
    ),
    (
        "drop the flag guard of the sign-mask rule",
        "  else match (isNSW || isNUW) && signMask op1, xorSignMask op0 with",
        "  else match signMask op1, xorSignMask op0 with",
        True,
        "signMask.no_flags",
    ),
]


def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("--timeout", type=int, default=300, help="seconds for each process")
    parser.add_argument("--memory", type=int, default=2000, help="MB for each Lean process")
    parser.add_argument("--keep", action="store_true", help="keep the temporary directory, and print it")
    args = parser.parse_args()
    if not os.environ.get("LLVM_PROJECT_SRC"):
        print("LLVM_PROJECT_SRC isn't set: run inside nix develop", file=sys.stderr)
        return 2
    src = Path(os.environ["LLVM_PROJECT_SRC"])
    run = Runner(args.timeout, args.memory)
    scope = "yes" if run.capped else "no"
    print(f"limits: {args.timeout} s and {args.memory} MB a process, systemd scope: {scope}")
    anchors = json.loads((HERE / "anchors.json").read_text())
    cited = "\n".join((HERE / f).read_text() for f in LEAN_FILES) + DOC.read_text()
    model = (HERE / "SimplifyAddModel.lean").read_text()
    failed = False
    clock = [time.monotonic()]

    def report(name: str, problems: list[str]) -> None:
        nonlocal failed
        now = time.monotonic()
        print(f"{'ok  ' if not problems else 'FAIL'}  {name} ({now - clock[0]:.1f} s)", flush=True)
        clock[0] = now
        for p in problems[:40]:
            print(f"      {p}")
        failed |= bool(problems)

    work = Path(tempfile.mkdtemp(prefix="ir-lean-correspondence-"))
    try:
        report("pin: llvm-project, opt and the inventory are the pinned LLVM", check_pin(run, anchors, src))
        quotes = f"{len(anchors['anchors'])} quotes of {len(anchors['files'])} files"
        report(f"anchors: {quotes} say what's recorded", check_anchors(src, anchors, cited))
        report(
            "anchors: a changed line and a missing anchor are refused", anchor_negatives(src, anchors, cited)
        )

        error = build(run, work / "model", model)
        ok = error is None
        report(
            "lean: the model and simplifyAddInst_sound compile, warnings as errors",
            [error[-3000:]] if error else [],
        )
        if ok:
            env = {"LEAN_PATH": str(work / "model"), "IRLEAN_CHECK_MODULE": "SimplifyAddSound"}
            ax = run(run.lean(str(ROOT / "tests" / "check_axioms.lean")), env)
            replay = run(["leanchecker", "SimplifyAddSound"], {"LEAN_PATH": str(work / "model")})
            problems = [] if ax.returncode == 0 else [ax.stdout + ax.stderr]
            problems += [] if replay.returncode == 0 else [replay.stdout + replay.stderr]
            report(f"lean: axioms {ax.stdout.strip()}, and leanchecker replays it", problems)

        all_cases = cases()
        (work / "cases.ll").write_text(module(all_cases))
        before = run(["opt", "-S", "-passes=verify", str(work / "cases.ll")])
        after = run(["opt", "-S", "-passes=instsimplify", str(work / "cases.ll")])
        if before.returncode != 0 or after.returncode != 0:
            report("differential: opt runs", [before.stderr[-2000:], after.stderr[-2000:]])
            return 1
        if ok:
            r = compare(all_cases, answers(run, work / "model", all_cases), before.stdout, after.stdout)
            report(
                f"differential: {r['compared']} of {len(all_cases)} cases match opt -passes=instsimplify, "
                f"{r['delegated']} delegated, {r['operand_changed']} left out since an operand changed first",
                r["mismatches"] + r["sentinel_problems"] + ([] if r["compared"] else ["nothing compared"]),
            )

        for name, old, new, proves, catches in MUTANTS:
            assert model.count(old) == 1, f"mutant {name}: the model doesn't have its line once"
            shutil.rmtree(work / "mutant", ignore_errors=True)
            # A mutant can leave a flag unused, which is a warning, so it compiles without warnings as errors.
            error = build(run, work / "mutant", model.replace(old, new), strict=False)
            problems = []
            if error is not None and error.startswith("SimplifyAddModel: "):
                report(f"mutant: {name}", [f"the model doesn't compile: {error[-1500:]}"])
                continue
            if proves and error is not None:
                problems.append(f"the theorem fails: {error[-1500:]}")
            elif not proves and (error is None or not error.startswith("SimplifyAddSound: ")):
                problems.append(f"the theorem doesn't fail with an error of its own: {(error or '')[-1500:]}")
            r = compare(all_cases, answers(run, work / "mutant", all_cases), before.stdout, after.stdout)
            if not any(m.startswith(f"{catches}:") for m in r["mismatches"]):
                problems.append(f"opt doesn't disagree on {catches}: {r['mismatches'][:5]}")
            verdict = "still proves" if proves else "fails to prove"
            differ = f"{len(r['mismatches'])} cases differ from opt"
            report(f"mutant: {name}: the theorem {verdict}, and {differ}", problems)
    except Unknown as e:
        print(
            f"UNKNOWN  {e}: a limit stopped a step, so this run is neither a pass nor a failure of the model"
        )
        return 1
    finally:
        if args.keep:
            print(f"kept {work}")
        else:
            shutil.rmtree(work, ignore_errors=True)
    print("FAIL" if failed else "ok    all checks passed")
    return 1 if failed else 0


def anchor_negatives(src: Path, anchors: dict, cited: str) -> list[str]:
    """A copy of the source with one quoted line changed, and anchors with one removed, are each refused."""
    problems = []
    with tempfile.TemporaryDirectory() as tmp:
        for name in anchors["files"]:
            (Path(tmp) / name).parent.mkdir(parents=True, exist_ok=True)
            shutil.copy(src / name, Path(tmp) / name)
        target = Path(tmp) / "llvm/lib/Analysis/InstructionSimplify.cpp"
        target.chmod(0o644)
        text = target.read_text()
        assert text.count("  if (IsNUW && match(Op1, m_AllOnes()))") == 1
        target.write_text(
            text.replace("  if (IsNUW && match(Op1, m_AllOnes()))", "  if (match(Op1, m_AllOnes()))")
        )
        got = check_anchors(Path(tmp), anchors, cited)
        if not any(p.startswith("anchor add.nuwAllOnes:") for p in got):
            problems.append(f"a changed line isn't refused: {got}")
    fewer = {**anchors, "anchors": [a for a in anchors["anchors"] if a["id"] != "add.signMask"]}
    got = check_anchors(src, fewer, cited)
    if not any("InstructionSimplify.cpp:631 is code no anchor quotes" in p for p in got):
        problems.append(f"a missing anchor isn't refused: {got}")
    return problems


if __name__ == "__main__":
    sys.exit(main())
