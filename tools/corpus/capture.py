#!/usr/bin/env python3
"""Captures what an `opt` pipeline does to IR, one pass at a time: a corpus of real (before, after) pairs,
each the exact module before a pass that changed it and after. They're problems for the superoptimizer and
sources of lemmas. docs/corpus.md says what the corpus is for and what each record holds.

  capture  Runs `opt -passes=SPEC` on each input twice, and the two outputs have to agree. Runs it once
           more with -print-changed -print-module-scope, so each pass that changed the module is a step,
           with the module before and after it. Each step is then replayed alone, and is `reproduced`
           only if that gives its `after` byte for byte.
  pin      Prints the toolchain a capture records: opt's path, hash and version, and the pipeline it
           prints for SPEC. `--check` fails unless opt is the repo's pinned LLVM, the pipeline is the
           inventory's byte for byte, and a corpus already in OUT was made by this same opt and pipeline.

The corpus is generated on demand and never committed: build/corpus/SPEC by default, which git ignores. With
no inputs, `capture` reads tools/corpus/seeds/*.ll.

usage: tools/corpus/capture.py capture [--passes SPEC] [--mtriple TRIPLE] [--out DIR] [--jobs N] [INPUT ...]
       tools/corpus/capture.py pin [--passes SPEC] [--mtriple TRIPLE] [--out DIR] [--check]
"""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tomllib
from pathlib import Path
from typing import Any

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
SEEDS = HERE / "seeds"
INVENTORY = ROOT / "tests" / "llvm_scope" / "inventory.json"
TARGETS = ROOT / "tests" / "llvm" / "targets.toml"
SCHEMA = "ir-lean.corpus.capture/1"
PIN_SCHEMA = "ir-lean.corpus.pin/1"
SPEC = "default<O1>"
# The triple the repo's proofs, the inventory and tools/binding.py use, so a pair captured on a Mac is the
# same IR as one captured on Linux.
MTRIPLE = "x86_64-unknown-linux-gnu"
TIMEOUT_S = 120

# Adaptors that run the passes inside them and aren't passes of their own.
# `coro-cond` runs its passes only on a module that declares a coroutine intrinsic.
ADAPTOR_NAMES = {"function", "cgscc", "devirt", "loop", "loop-mssa", "module", "coro-cond"}
# What -debug-pass-manager reports as passes but the printed pipeline doesn't list as one: `devirt<4>` and
# `coro-cond` themselves, and the printer or writer opt adds for its output, which is part of the invocation.
NOT_PASSES = {"DevirtSCCRepeatedPass", "CoroConditionalWrapper", "PrintModulePass", "BitcodeWriterPass"}


def read_json(path: Path) -> Any:
    return json.loads(path.read_text())


def write_json(path: Path, data: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=1, sort_keys=True, ensure_ascii=False) + "\n")


def sha256_bytes(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def sha256_file(p: Path) -> str:
    with p.open("rb") as f:
        return hashlib.file_digest(f, "sha256").hexdigest()


def slug(text: str) -> str:
    return re.sub(r"[^A-Za-z0-9_.-]+", "-", text).strip("-")


def opt_argv(opt: str, passes: str, mtriple: str) -> list[str]:
    """opt as tools/binding.py runs it: the input on stdin, so the output names no path."""
    return [opt, "-S", f"-passes={passes}", "-", "-o", "-", f"-mtriple={mtriple}"]


def run(argv: list[str], stdin: bytes, timeout: float) -> tuple[int, bytes, str]:
    """The exit code, stdout and stderr. A timeout is exit code -1."""
    try:
        r = subprocess.run(argv, input=stdin, capture_output=True, timeout=timeout, check=False)
    except subprocess.TimeoutExpired:
        return -1, b"", f"timed out after {timeout} s"
    return r.returncode, r.stdout, r.stderr.decode(errors="replace")


# ------------------------------------------------------------------------------------------------------------
# pin


def derive_pin(spec: str, mtriple: str) -> dict:
    """The toolchain a capture runs: opt by path, hash and version, and the pipeline it prints for `spec`. On
    Nix, opt's runpath names the store path of the libLLVM it loads, so its hash changes with that library."""
    found = shutil.which("opt")
    if found is None:
        sys.exit("no opt on PATH: run this in `nix develop`")
    opt = Path(found).resolve()
    code, out, err = run([str(opt), "--version"], b"", 30)
    if code != 0:
        sys.exit(f"{opt} --version failed: {err[-400:]}")
    # The host CPU line names the machine, not the binary.
    version = [x.strip() for x in out.decode().splitlines() if x.strip() and "Host CPU" not in x]
    argv = [str(opt), "-disable-output", f"-passes={spec}", f"-mtriple={mtriple}", "-print-pipeline-passes"]
    code, out, err = run(argv, b"", 30)
    if code != 0:
        sys.exit(f"opt can't build the pipeline {spec}: {err[-400:]}")
    pipeline = out.decode().strip()
    tag = re.search(r"LLVM version (\S+)", "\n".join(version))
    project = tomllib.loads(TARGETS.read_text())["project"]
    inventory = read_json(INVENTORY)["pipelines"]["opt"].get(spec)
    return {
        "schema": PIN_SCHEMA,
        "opt": {"path": str(opt), "sha256": sha256_file(opt), "version": version},
        "llvm": {
            "tag": f"llvmorg-{tag.group(1)}" if tag else None,
            "repo_tag": project["tag"],
            "repo_commit": project["commit"],
        },
        "spec": spec,
        "mtriple": mtriple,
        "pipeline": {
            "text": pipeline,
            "sha256": sha256_bytes(pipeline.encode()),
            # None when the inventory has no entry for this spec to compare with.
            "inventory_match": None if inventory is None else pipeline == inventory["pipeline"],
        },
    }


def pin_problems(pin: dict, recorded: dict | None) -> list[str]:
    """Why `pin` can't make or add to a corpus: an opt that isn't the repo's LLVM, a pipeline that isn't the
    inventory's, or a corpus that another opt or pipeline made."""
    problems = []
    if pin["llvm"]["tag"] != pin["llvm"]["repo_tag"]:
        problems.append(f"opt is {pin['llvm']['tag']}, not the repo's pin {pin['llvm']['repo_tag']}")
    if pin["pipeline"]["inventory_match"] is False:
        problems.append(f"the pipeline opt prints for {pin['spec']} isn't the inventory's")
    if recorded is not None:
        for what, mine, theirs in (
            ("opt", pin["opt"]["sha256"], recorded["opt"]["sha256"]),
            ("pipeline", pin["pipeline"]["sha256"], recorded["pipeline"]["sha256"]),
            ("pass spec", pin["spec"], recorded["spec"]),
            ("triple", pin["mtriple"], recorded["mtriple"]),
        ):
            if mine != theirs:
                problems.append(
                    f"the corpus there was made with {what} {theirs[:16]}, not {mine[:16]}: "
                    "capture into another --out, or delete it"
                )
    return problems


def default_out(spec: str) -> Path:
    return ROOT / "build" / "corpus" / slug(spec)


def recorded_pin(out: Path) -> dict | None:
    path = out / "pin.json"
    return read_json(path) if path.exists() else None


def cmd_pin(args: argparse.Namespace) -> int:
    pin = derive_pin(args.passes, args.mtriple)
    if not args.check:
        print(json.dumps(pin, indent=1, sort_keys=True))
        return 0
    out = args.out or default_out(args.passes)
    recorded = recorded_pin(out)
    problems = pin_problems(pin, recorded)
    for p in problems:
        print(p, file=sys.stderr)
    if not problems:
        inventory = {True: "the inventory's", None: "not in the inventory"}[
            pin["pipeline"]["inventory_match"]
        ]
        where = f", and made {out}" if recorded else ""
        opt = f"opt {pin['opt']['sha256'][:12]} is {pin['llvm']['tag']}"
        print(f"pin holds: {opt}, its {args.passes} is {inventory}{where}")
    return 1 if problems else 0


# ------------------------------------------------------------------------------------------------------------
# The pipeline opt prints, read into the passes it runs and the adaptors around each one.


def split_top(text: str) -> list[str]:
    """`text`'s elements, split at commas outside any <> or ()."""
    out, cur, depth = [], "", 0
    for c in text:
        depth += (c in "<(") - (c in ">)")
        if depth < 0:
            raise ValueError(f"unbalanced pipeline at {cur!r}")
        if c == "," and depth == 0:
            out.append(cur)
            cur = ""
        else:
            cur += c
    if depth != 0:
        raise ValueError("unbalanced pipeline")
    if cur:
        out.append(cur)
    return out


def parse_element(text: str) -> dict:
    """`name<params>(children)`, each part but the name optional. Params are kept as printed."""
    m = re.match(r"[A-Za-z0-9_.-]+", text)
    if m is None:
        raise ValueError(f"no pass name in {text!r}")
    name, rest = m.group(0), text[m.end() :]
    params = None
    if rest.startswith("<"):
        depth = 0
        for i, c in enumerate(rest):
            depth += (c == "<") - (c == ">")
            if depth == 0:
                params, rest = rest[1:i], rest[i + 1 :]
                break
    children = None
    if rest.startswith("(") and rest.endswith(")"):
        children = [parse_element(e) for e in split_top(rest[1:-1])]
        rest = ""
    if rest:
        raise ValueError(f"can't read {text!r}")
    return {"name": name, "params": params, "children": children}


def spec_of(e: dict) -> str:
    return e["name"] + (f"<{e['params']}>" if e["params"] is not None else "")


def unit_of(context: list[str]) -> str:
    for a in reversed(context):
        base = a.split("<")[0]
        if base in ("loop", "loop-mssa"):
            return "loop"
        if base in ("cgscc", "devirt"):
            return "cgscc"
        if base == "function":
            return "function"
    return "module"


def replay_specs(spec: str, context: list[str]) -> list[str]:
    """Pass specs that run one step alone: in its own unit's adaptor first, then in every adaptor around
    it."""
    unit = unit_of(context)
    if unit == "module":
        first = spec
    elif unit == "function":
        first = f"function({spec})"
    elif unit == "cgscc":
        first = f"cgscc({spec})"
    else:
        loop = next(a for a in reversed(context) if a.split("<")[0] in ("loop", "loop-mssa"))
        first = f"function({loop.split('<')[0]}({spec}))"
    full = spec
    for a in reversed(context):
        full = f"{a}({full})"
    return [first] if full == first else [first, full]


def flatten(elements: list[dict], context: list[str] | None = None, prefix: str = "") -> list[dict]:
    """Every pass the pipeline lists, in order, with the adaptors around it and where it is: `16.1.3` is the
    third pass in the first element of the sixteenth."""
    context = context or []
    out = []
    for i, e in enumerate(elements, 1):
        pos = f"{prefix}{i}"
        if e["children"] is not None:
            if e["name"] not in ADAPTOR_NAMES:
                raise ValueError(f"{spec_of(e)} at {pos} has children and isn't a known adaptor")
            out += flatten(e["children"], [*context, spec_of(e)], f"{pos}.")
        else:
            # `require<X>` and `invalidate<X>` are named with their analysis.
            name = spec_of(e) if e["name"] in ("require", "invalidate") else e["name"]
            out.append(
                {
                    "pos": pos,
                    "name": name,
                    "spec": spec_of(e),
                    "unit": unit_of(context),
                    "replay": replay_specs(spec_of(e), context),
                }
            )
    return out


def pipeline_passes(text: str) -> tuple[list[dict], dict[str, str]]:
    """The passes `text` lists, each with the new pass manager class the inventory registers it as, and every
    registered class's pass name, for the passes opt runs that the pipeline doesn't list."""
    leaves = flatten([parse_element(e) for e in split_top(text)])
    items = {i["name"]: i for i in read_json(INVENTORY)["items"]}
    named: dict[str, set[str]] = {}
    for name, item in items.items():
        for r in item["registrations"]:
            if r["registry"] != "legacy" and r.get("class"):
                named.setdefault(r["class"], set()).add(name)
    # A class registered under several names, such as ModuleInlinerWrapperPass, gets the one the pipeline
    # lists, or else the shortest.
    listed = {x["name"] for x in leaves}
    names = {cls: min(ns, key=lambda n: (n not in listed, len(n), n)) for cls, ns in named.items()}
    for leaf in leaves:
        leaf["class"] = class_of(leaf, items)
    return leaves, names


def class_of(leaf: dict, items: dict[str, dict]) -> str | None:
    if leaf["name"].startswith("require<"):
        return "RequireAnalysisPass<"
    if leaf["name"].startswith("invalidate<"):
        return "InvalidateAnalysisPass<"
    item = items.get(leaf["name"])
    if item is None:
        return None
    regs = [r for r in item["registrations"] if r["registry"] != "legacy" and r.get("class")]
    same = [r for r in regs if r.get("unit") == leaf["unit"]] or regs
    return same[0]["class"] if same else None


# ------------------------------------------------------------------------------------------------------------
# capture

RUN = re.compile(r"^Running pass: (.+?) on (.+?)(?: \(\d+ (?:instructions?|nodes?)\))?$")
DUMP = re.compile(r"^\*\*\* IR Dump After (.+?) on (.+?)( omitted because no change| filtered out)? \*\*\*$")
START = "*** IR Dump At Start ***"
# Lines -debug-pass-manager and -print-changed write between dumps. Anything else after a dump header is IR.
CONTROL = (
    "Running pass: ",
    "Running analysis: ",
    "*** IR ",
    "Invalidating ",
    "Clearing all analysis",
    "Skipping ",
)


def parse_trace(text: str) -> list[dict]:
    """The passes and dumps of a -debug-pass-manager -print-changed -print-module-scope run, in order. A
    changed dump carries the module after the pass."""
    events: list[dict] = []
    module: list[str] | None = None
    for line in text.splitlines():
        if module is not None and not line.startswith(CONTROL):
            module.append(line)
            continue
        if module is not None:
            events[-1]["module"] = "\n".join(module).rstrip("\n") + "\n"
            module = None
        if line == START:
            events.append({"kind": "start"})
            module = []
        elif m := RUN.match(line):
            events.append({"kind": "run", "class": m.group(1), "unit": m.group(2)})
        elif m := DUMP.match(line):
            changed = m.group(3) is None
            events.append({"kind": "dump", "class": m.group(1), "unit": m.group(2), "changed": changed})
            if changed:
                module = []
    if module is not None:
        events[-1]["module"] = "\n".join(module).rstrip("\n") + "\n"
    return events


def class_matches(cls: str, want: str | None) -> bool:
    if want is None:
        return False
    return cls.startswith(want) if want.endswith("<") else cls == want


def attribute(events: list[dict], leaves: list[dict], names: dict[str, str]) -> dict:
    """The steps of a traced run: each pass that changed the module, matched to the pipeline's passes in
    order, with the module before and after it. A pass the pipeline doesn't list, such as the loop-simplify
    and lcssa every loop adaptor runs first, is implicit and named by its class. Loop, CGSCC and function
    passes may run again, once per loop, per SCC or per devirtualization round."""
    cursor = 0
    current: dict[str, Any] | None = None
    steps: list[dict] = []
    start = next((e.get("module") for e in events if e["kind"] == "start"), None)
    module = start
    for e in events:
        if e["kind"] == "run" and e["class"] in NOT_PASSES:
            current = None
        elif e["kind"] == "run":
            idx = next(
                (i for i in range(cursor, len(leaves)) if class_matches(e["class"], leaves[i]["class"])), None
            )
            again = False
            if idx is None:
                idx = next(
                    (
                        i
                        for i in range(cursor - 1, -1, -1)
                        if leaves[i]["unit"] in ("loop", "cgscc", "function")
                        and class_matches(e["class"], leaves[i]["class"])
                    ),
                    None,
                )
                again = idx is not None
            if idx is not None:
                if not again:
                    cursor = idx + 1
                leaf = leaves[idx]
                current = {"pos": leaf["pos"], "name": leaf["name"], "spec": leaf["spec"], "again": again}
                current |= {"replay": leaf["replay"], "implicit": False}
            else:
                name = names.get(e["class"])
                current = {"pos": None, "name": name or f"?{e['class']}", "spec": name, "again": False}
                current |= {"replay": [f"function({name})"] if name else [], "implicit": True}
                # Where it ran: just before this position, such as the loop adaptor it canonicalizes for.
                current["before_pos"] = leaves[cursor]["pos"] if cursor < len(leaves) else None
            current |= {"class": e["class"], "unit": e["unit"]}
        # A wrapper's dump repeats the module after the last pass it ran, which is a step already.
        elif e["kind"] == "dump" and e["changed"] and e["class"] not in NOT_PASSES:
            if current is None or current["class"] != e["class"]:
                current = {"pos": None, "name": f"?{e['class']}", "spec": None, "again": False}
                current |= {"replay": [], "implicit": True, "class": e["class"], "unit": e["unit"]}
            after = e.get("module") or ""
            steps.append({**current, "before": module, "after": after})
            module = after
    return {"start": start, "final": module, "steps": steps}


PREDS = re.compile(r"\s+; preds = .*$", re.MULTILINE)


def without_comments(ll: str) -> str:
    """The IR without its `; preds =` comments and comment lines, which LLVM writes from use-list order. Text
    round trips don't keep that order, so a replay can differ in these and nothing else."""
    return "\n".join(x for x in PREDS.sub("", ll).splitlines() if not x.startswith(";"))


def capture_case(path: Path, pin: dict, leaves: list[dict], names: dict[str, str], out: Path) -> dict:
    """Captures one input into `out`/its name, and returns its record."""
    name = path.stem
    case = out / name
    if case.exists():
        shutil.rmtree(case)
    data = path.read_bytes()
    opt, spec, mtriple = pin["opt"]["path"], pin["spec"], pin["mtriple"]
    record: dict[str, Any] = {
        "schema": SCHEMA,
        "case": name,
        "source": str(path),
        "spec": spec,
        "mtriple": mtriple,
        "opt_sha256": pin["opt"]["sha256"],
        "pipeline_sha256": pin["pipeline"]["sha256"],
        "input_sha256": sha256_bytes(data),
    }
    triple = re.search(r'^target triple = "([^"]*)"', data.decode(errors="replace"), re.M)
    if triple is None or triple.group(1) != mtriple:
        found = triple.group(1) if triple else "missing"
        return record | {"status": "refused", "reason": f"its target triple is {found}, not {mtriple}"}
    argv = opt_argv(opt, spec, mtriple)
    first = run(argv, data, TIMEOUT_S)
    again = run(argv, data, TIMEOUT_S)
    traced = run([*argv, "-debug-pass-manager", "-print-changed", "-print-module-scope"], data, TIMEOUT_S)
    # The input as opt prints it, which is what the trace starts from.
    printed = run(opt_argv(opt, "verify", mtriple), data, TIMEOUT_S)
    for label, (code, _, err) in (
        ("run", first),
        ("second run", again),
        ("traced run", traced),
        ("verify", printed),
    ):
        if code != 0:
            return record | {"status": "error", "reason": f"opt failed on the {label}: {err[-400:]}"}
    found = attribute(parse_trace(traced[2]), leaves, names)
    output = first[1]
    checks = {
        "deterministic": output == again[1],
        "trace_output_matches": traced[1] == output,
        "trace_starts_from_input": found["start"] == printed[1].decode(),
        "trace_ends_at_output": found["final"] == output.decode(),
    }
    (case / "steps").mkdir(parents=True)
    (case / "input.ll").write_bytes(data)
    (case / "output.ll").write_bytes(output)
    steps = []
    for k, s in enumerate(found["steps"], 1):
        before, after = s["before"] or "", s["after"]
        replay, comments_only = None, False
        for alone in s["replay"]:
            code, got, _ = run(opt_argv(opt, alone, mtriple), before.encode(), TIMEOUT_S)
            if code == 0 and got.decode() == after:
                replay = alone
                break
            comments_only |= code == 0 and without_comments(got.decode()) == without_comments(after)
        d = Path("steps") / f"{k:02d}-{slug(s['name'])}"
        (case / d).mkdir()
        (case / d / "before.ll").write_text(before)
        (case / d / "after.ll").write_text(after)
        step = {k2: s.get(k2) for k2 in ("pos", "name", "spec", "class", "unit", "implicit", "again")}
        if s["implicit"]:
            step["before_pos"] = s.get("before_pos")
        steps.append(
            step
            | {
                "k": k,
                "before": str(d / "before.ll"),
                "after": str(d / "after.ll"),
                "before_sha256": sha256_bytes(before.encode()),
                "after_sha256": sha256_bytes(after.encode()),
                "replay_tried": s["replay"],
                "replay": replay,
                "reproduced": replay is not None,
                "replay_differs_only_in_comments": comments_only and replay is None,
            }
        )
    status = "captured" if all(checks.values()) else "inconsistent"
    return record | checks | {"status": status, "output_sha256": sha256_bytes(output), "steps": steps}


def cmd_capture(args: argparse.Namespace) -> int:
    pin = derive_pin(args.passes, args.mtriple)
    out = args.out or default_out(args.passes)
    if problems := pin_problems(pin, recorded_pin(out)):
        for p in problems:
            print(f"{out}: {p}", file=sys.stderr)
        return 1
    inputs = [Path(p) for p in args.inputs] or sorted(SEEDS.glob("*.ll"))
    stems = [p.stem for p in inputs]
    if dup := sorted({s for s in stems if stems.count(s) > 1}):
        sys.exit(f"two inputs would be the same case: {dup}")
    write_json(out / "pin.json", pin)
    leaves, names = pipeline_passes(pin["pipeline"]["text"])
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        records = list(pool.map(lambda p: capture_case(p, pin, leaves, names, out), inputs))
    bad = 0
    for r in records:
        write_json(out / r["case"] / "capture.json", r)
        steps = r.get("steps", [])
        alone = sum(1 for s in steps if s["reproduced"])
        why = f": {r['reason']}" if "reason" in r else ""
        print(f"{r['case']}: {r['status']}{why}, {len(steps)} steps changed it, {alone} replayed alone")
        bad += r["status"] != "captured"
    print(f"{out}: {len(records) - bad} of {len(records)} inputs captured")
    return 1 if bad else 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    for name in ("capture", "pin"):
        p = sub.add_parser(name)
        p.add_argument("--passes", default=SPEC, help=f"the pass spec opt runs, by default {SPEC}")
        p.add_argument(
            "--mtriple", default=MTRIPLE, help="the target triple, which each input has to declare"
        )
        p.add_argument("--out", type=Path, help="the corpus directory, by default build/corpus/SPEC")
        if name == "capture":
            p.add_argument("--jobs", type=int, default=min(8, os.cpu_count() or 1))
            p.add_argument("inputs", nargs="*", help="LLVM IR files, by default tools/corpus/seeds/*.ll")
        else:
            p.add_argument("--check", action="store_true")
    args = ap.parse_args()
    return cmd_capture(args) if args.cmd == "capture" else cmd_pin(args)


if __name__ == "__main__":
    sys.exit(main())
