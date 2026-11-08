#!/usr/bin/env python3
"""The O1 campaign: what `opt -passes=default<O1>` does, pass by pass, on one pinned configuration, and
what of it is proved. docs/o1-campaign.md has the configuration, the rules for counting, and what the
numbers mean.

  pin       Records the pinned opt, by hash and Nix provenance, the LLVM source, the triple and data
            layout, and the exact pipeline opt prints for default<O1>, which has to be the merged
            inventory's. `--check` derives it again and fails on any difference.
  pipeline  Parses that pipeline into its positions: each pass with its parameters, the adaptors around
            it, its IR unit, its inventory entry and its family.
  capture   Runs the pinned invocation on each input, twice, and once more with -print-changed, so each
            pass that changed the module is a step with the exact IR before and after it. Each step is
            replayed alone, and has to give the same IR byte for byte to be bound.
  bind      For each step tools/binding.py can judge, and for the whole default<O1> run, writes a
            certificate, records a bundle and has tools/binding.py verify it. Its verdict is kept as is.
  ledger    Counts obligations, evidence and blockers. Nothing but a `bound` verdict counts as evidence,
            and no evidence of this kind finishes a pass, a family, or O1.
  check     Checks that the committed files agree: every pass has one family, the pin and pipeline are
            the inventory's, and the ledger is what `ledger` derives from the evidence.

Everything here is translation validation of single runs. None of it is all-input pass correctness, a
binding to LLVM's C++, or composition of the pipeline.

usage: campaign/o1/o1.py pin [--check]
       campaign/o1/o1.py pipeline
       campaign/o1/o1.py capture [CASE.ll ...]
       campaign/o1/o1.py bind [--case NAME ...] [--workers N]
       campaign/o1/o1.py ledger
       campaign/o1/o1.py check
"""

from __future__ import annotations

import argparse
import concurrent.futures
import contextlib
import hashlib
import importlib.util
import json
import os
import platform
import re
import shutil
import subprocess
import sys
import tempfile
import time
import tomllib
from pathlib import Path
from typing import Any

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(HERE))
import measure  # noqa: E402

CONFIG = HERE / "config.json"
FAMILIES = HERE / "families.json"
PIN = HERE / "pin.json"
PIPELINE = HERE / "pipeline.json"
LEDGER = HERE / "ledger.json"
CORPUS = HERE / "corpus"
EVIDENCE = HERE / "evidence"
MEASUREMENTS = HERE / "measurements"
INVENTORY = ROOT / "tests" / "llvm_scope" / "inventory.json"
TARGETS = ROOT / "tests" / "llvm" / "targets.toml"
BINDING = ROOT / "tools" / "binding.py"
TOOL = ROOT / "build" / "ir-lean"
WORK = ROOT / "build" / "o1"

LEVEL = "O1"
# Adaptors, pass managers and wrappers opt runs that aren't passes of their own. The printed pipeline
# names what they run.
ADAPTOR_NAMES = {"function", "cgscc", "devirt", "loop", "loop-mssa", "module"}
# `devirt<4>` itself, which -debug-pass-manager reports as a pass.
ADAPTOR_CLASSES = {"DevirtSCCRepeatedPass"}
# What opt adds for -S, after default<O1>: part of the invocation, not of the pipeline.
OPT_OUTPUT_CLASSES = {"PrintModulePass", "BitcodeWriterPass"}
# What a verdict from tools/binding.py can be. Only `bound` is evidence.
STATUSES = ("bound", "refused", "unsupported", "unknown", "error")


def load_binding() -> Any:
    spec = importlib.util.spec_from_file_location("ir_lean_binding", BINDING)
    if spec is None or spec.loader is None:
        sys.exit(f"can't load {BINDING}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def read_json(path: Path) -> Any:
    return json.loads(path.read_text())


def write_json(path: Path, data: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=1, sort_keys=True, ensure_ascii=False) + "\n")


def sha256_bytes(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def sha256_file(p: Path) -> str:
    return sha256_bytes(p.read_bytes())


def host_key() -> str:
    return f"{platform.machine()}-{sys.platform}"


def sh(argv: list[str], stdin: bytes | None = None) -> str:
    r = subprocess.run(argv, input=stdin, capture_output=True, check=False)
    if r.returncode != 0:
        sys.exit(f"{' '.join(argv)} failed: {r.stderr.decode(errors='replace')[-400:]}")
    return r.stdout.decode()


# ------------------------------------------------------------------------------------------------------------
# pin


def derive_pin(cfg: dict) -> dict:
    opt = shutil.which("opt")
    if opt is None:
        sys.exit("no opt on PATH: run this in `nix develop`")
    real = Path(opt).resolve()
    version = sh([str(real), "--version"])
    # The host CPU line names the machine, not the binary.
    version_lines = [x.strip() for x in version.splitlines() if x.strip() and "Host CPU" not in x]
    project = tomllib.loads(TARGETS.read_text())["project"]
    found = re.search(r"LLVM version (\S+)", version)
    if found is None or "llvmorg-" + found.group(1) != project["tag"]:
        sys.exit(f"opt is {version_lines}, not {project['tag']}")
    if cfg["llvm_tag"]["commit"] != project["commit"] or cfg["llvm_tag"]["tag"] != project["tag"]:
        sys.exit("config.json's llvm_tag isn't tests/llvm/targets.toml's pin")
    src = os.environ.get("LLVM_PROJECT_SRC")
    if not src:
        sys.exit("LLVM_PROJECT_SRC isn't set: run this in `nix develop`")
    nar = sh(["nix", "hash", "path", src]).strip()
    if nar != project["nix_hash"]:
        sys.exit(f"LLVM_PROJECT_SRC hashes to {nar}, not the pinned {project['nix_hash']}")
    store = Path(*real.parts[:4])
    info = json.loads(sh(["nix", "path-info", "--json", str(store)]))
    entry = info[str(store)] if isinstance(info, dict) else info[0]
    signatures = sorted(entry.get("signatures") or [])
    pipeline = sh(
        [
            str(real),
            "-disable-output",
            f"-passes={cfg['spec']}",
            f"-mtriple={cfg['mtriple']}",
            "-print-pipeline-passes",
        ],
        stdin=b"",
    ).strip()
    inventory = read_json(INVENTORY)["pipelines"]["opt"][cfg["spec"]]["pipeline"]
    binding = load_binding()
    return {
        "opt": {
            "path": str(real),
            "sha256": sha256_file(real),
            "version": version_lines,
            "store_path": str(store),
            "nar_hash": entry.get("narHash"),
            "deriver": entry.get("deriver"),
            "signatures": signatures,
            "provenance": (
                "substituted from cache.nixos.org, which signed it"
                if any(s.startswith("cache.nixos.org-1:") for s in signatures)
                else "not signed by cache.nixos.org: built here or elsewhere"
            ),
        },
        "llvm": {
            "repository": project["repository"],
            "tag": project["tag"],
            "commit": project["commit"],
            "tag_object": cfg["llvm_tag"]["tag_object"],
            "tag_checked": cfg["llvm_tag"]["checked"],
            "nix_hash": nar,
            "source": src,
        },
        "invocation": binding.opt_argv("opt", cfg["spec"], cfg["mtriple"]),
        "target": {
            "triple": cfg["mtriple"],
            "datalayout": cfg["datalayout"],
            "cpu": cfg["cpu"],
            "features": cfg["features"],
        },
        "options": cfg["options"],
        "pipeline": {
            "text": pipeline,
            "sha256": sha256_bytes(pipeline.encode()),
            "inventory_match": pipeline == inventory,
        },
        "lean": {
            "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
            "version": sh(["lean", "--version"]).strip(),
        },
    }


def cmd_pin(args: argparse.Namespace) -> int:
    cfg = read_json(CONFIG)
    derived = derive_pin(cfg)
    if not derived["pipeline"]["inventory_match"]:
        print("the pipeline opt prints isn't the inventory's for default<O1>", file=sys.stderr)
    pin: dict[str, Any] = read_json(PIN) if PIN.exists() else {"schema": "ir-lean.o1.pin/1", "hosts": {}}
    hosts: dict[str, Any] = pin["hosts"]
    pin.update(level=LEVEL, spec=cfg["spec"])
    if args.check:
        recorded = hosts.get(host_key())
        if recorded != derived:
            diff = sorted(k for k in derived if (recorded or {}).get(k) != derived[k])
            print(f"the pin for {host_key()} differs in {diff}", file=sys.stderr)
            return 1
        print(f"pin for {host_key()} holds: opt {derived['opt']['sha256'][:12]}, {cfg['spec']}")
        return 0 if derived["pipeline"]["inventory_match"] else 1
    hosts[host_key()] = derived
    write_json(PIN, pin)
    print(PIN)
    return 0 if derived["pipeline"]["inventory_match"] else 1


def host_pin() -> dict:
    pin = read_json(PIN)
    if host_key() not in pin["hosts"]:
        sys.exit(f"no pin for {host_key()}: run `campaign/o1/o1.py pin`")
    return pin["hosts"][host_key()]


# ------------------------------------------------------------------------------------------------------------
# pipeline


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
    """`name<params>(children)`, each part but the name optional. Params are kept as printed, `<>`
    included."""
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


def family_name(e: dict) -> str:
    """The name families.json and the ledger use: the pass name, or `require<X>` and `invalidate<X>`."""
    return spec_of(e) if e["name"] in ("require", "invalidate") else e["name"]


def replay_specs(spec: str, context: list[str]) -> list[str]:
    """Pass specs to run one step alone: in its own unit's adaptor first, then in every adaptor around it."""
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
    """Every pass position, in the order the pipeline lists them, with the adaptors around it."""
    context = context or []
    out = []
    for i, e in enumerate(elements, 1):
        pos = f"{prefix}{i}"
        if e["children"] is not None:
            if e["name"] not in ADAPTOR_NAMES:
                raise ValueError(f"{spec_of(e)} at {pos} has children and isn't a known adaptor")
            out += flatten(e["children"], [*context, spec_of(e)], f"{pos}.")
        else:
            out.append(
                {
                    "pos": pos,
                    "name": family_name(e),
                    "spec": spec_of(e),
                    "context": context,
                    "unit": unit_of(context),
                    "replay": replay_specs(spec_of(e), context),
                }
            )
    return out


def adaptors(elements: list[dict], prefix: str = "") -> list[dict]:
    out = []
    for i, e in enumerate(elements, 1):
        if e["children"] is not None:
            out.append({"pos": f"{prefix}{i}", "spec": spec_of(e), "passes": len(flatten(e["children"]))})
            out += adaptors(e["children"], f"{prefix}{i}.")
    return out


def inventory_index() -> tuple[dict[str, dict], dict[str, str]]:
    """Inventory items by name, and the new pass manager's class names to pass names. A class registered under
    several names, such as ModuleInlinerWrapperPass, gets the one families.json lists."""
    items = {i["name"]: i for i in read_json(INVENTORY)["items"]}
    named: dict[str, list[str]] = {}
    for name, item in items.items():
        for r in item["registrations"]:
            if r["registry"] != "legacy" and r.get("class"):
                named.setdefault(r["class"], []).append(name)
    fam = family_of(read_json(FAMILIES))
    classes = {}
    for cls, names in named.items():
        listed = sorted(n for n in set(names) if n in fam)
        classes[cls] = listed[0] if len(listed) == 1 else sorted(names)[0]
    return items, classes


def class_of(leaf: dict, items: dict[str, dict]) -> str | None:
    if leaf["name"].startswith("require<"):
        return "RequireAnalysisPass<"
    if leaf["name"].startswith("invalidate<"):
        return "InvalidateAnalysisPass<"
    item = items.get(leaf["name"])
    if item is None:
        return None
    unit = leaf["unit"]
    regs = [r for r in item["registrations"] if r["registry"] != "legacy" and r.get("class")]
    same = [r for r in regs if r.get("unit") == unit] or regs
    return same[0]["class"] if same else None


def family_of(families: dict) -> dict[str, str]:
    out: dict[str, str] = {}
    for fam, f in families["families"].items():
        for p in f["passes"]:
            if p in out:
                raise ValueError(f"{p} is in both {out[p]} and {fam}")
            out[p] = fam
    return out


def derive_pipeline(text: str) -> dict:
    elements = [parse_element(e) for e in split_top(text)]
    leaves = flatten(elements)
    items, _ = inventory_index()
    fam = family_of(read_json(FAMILIES))
    for leaf in leaves:
        base = leaf["name"].split("<")[1].rstrip(">") if "<" in leaf["name"] else leaf["name"]
        item = items.get(base)
        leaf["inventory_id"] = item["id"] if item else None
        leaf["class"] = class_of(leaf, items)
        leaf["family"] = fam.get(leaf["name"])
    distinct = sorted({x["name"] for x in leaves})
    by_family: dict[str, int] = {}
    for leaf in leaves:
        by_family[leaf["family"] or "?"] = by_family.get(leaf["family"] or "?", 0) + 1
    return {
        "schema": "ir-lean.o1.pipeline/1",
        "level": LEVEL,
        "spec": read_json(CONFIG)["spec"],
        "pipeline_sha256": sha256_bytes(text.encode()),
        "positions": len(leaves),
        "distinct_passes": len(distinct),
        "positions_by_family": dict(sorted(by_family.items())),
        "unfamilied": sorted({x["name"] for x in leaves if x["family"] is None}),
        "adaptors": adaptors(elements),
        "leaves": leaves,
    }


def cmd_pipeline(args: argparse.Namespace) -> int:
    data = derive_pipeline(host_pin()["pipeline"]["text"])
    write_json(PIPELINE, data)
    print(f"{PIPELINE}: {data['positions']} positions, {data['distinct_passes']} passes")
    return 1 if data["unfamilied"] else 0


# ------------------------------------------------------------------------------------------------------------
# capture

RUN = re.compile(r"^Running pass: (.+?) on (.+?)(?: \(\d+ (?:instructions?|nodes?)\))?$")
ANALYSIS = re.compile(r"^Running analysis: (.+?) on (.+)$")
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
    """The events of a -debug-pass-manager -print-changed -print-module-scope run, in order. A changed dump
    carries the module after the pass."""
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
        elif m := ANALYSIS.match(line):
            events.append({"kind": "analysis", "class": m.group(1), "unit": m.group(2)})
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


def attribute(events: list[dict], leaves: list[dict], classes: dict[str, str]) -> dict:
    """Matches each pass opt ran to its position in the printed pipeline, in order. A pass found nowhere in
    it, such as the loop-simplify and lcssa every loop adaptor runs first, is implicit, and named by its
    class. Loop and CGSCC positions may run again, once per loop or per devirtualization round."""
    cursor = 0
    current: dict[str, Any] | None = None
    invocation: list[str] = []
    runs: list[dict] = []
    steps: list[dict] = []
    analyses: dict[str, int] = {}
    start = next((e.get("module") for e in events if e["kind"] == "start"), None)
    module = start
    for e in events:
        if e["kind"] == "analysis":
            analyses[e["class"]] = analyses.get(e["class"], 0) + 1
        elif e["kind"] == "run" and e["class"] in ADAPTOR_CLASSES | OPT_OUTPUT_CLASSES:
            current = None
            if e["class"] in OPT_OUTPUT_CLASSES:
                invocation.append(e["class"])
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
                current |= {"family": leaf["family"], "replay": leaf["replay"], "implicit": False}
            else:
                name = classes.get(e["class"])
                current = {"pos": None, "name": name or f"?{e['class']}", "spec": name, "again": False}
                current |= {"family": None, "replay": [f"function({name})"] if name else [], "implicit": True}
                # Where it ran: just before this position, such as the loop adaptor it canonicalizes for.
                current["before_pos"] = leaves[cursor]["pos"] if cursor < len(leaves) else None
            current = {**current, "class": e["class"], "unit": e["unit"]}
            runs.append(current)
        elif e["kind"] == "dump" and e["changed"]:
            if current is None or current["class"] != e["class"]:
                current = {"pos": None, "name": f"?{e['class']}", "spec": None, "again": False}
                current |= {"family": None, "replay": [], "implicit": True, "class": e["class"]}
                current["unit"] = e["unit"]
            after = e.get("module") or ""
            steps.append({**current, "before": module, "after": after})
            module = after
    return {
        "start": start,
        "final": module,
        "runs": runs,
        "steps": steps,
        "analyses": analyses,
        "invocation": sorted(set(invocation)),
    }


def opt_run(
    argv: list[str], stdin: bytes, label: str, timeout: float, log: list[dict]
) -> tuple[int, bytes, str]:
    with tempfile.TemporaryFile() as i, tempfile.TemporaryFile() as o, tempfile.TemporaryFile() as e:
        i.write(stdin)
        i.seek(0)
        rec = measure.run(argv, label=label, timeout=timeout, cap_mb=4000, stdin=i, stdout=o, stderr=e)
        o.seek(0)
        e.seek(0)
        out, err = o.read(), e.read().decode(errors="replace")
    log.append(rec)
    code = rec["exit"] if rec["outcome"] in ("ok", "failed") else -1
    return code, out, err


def ir_report(ll: str) -> dict:
    """ir-lean's report on the one function a module defines: whether it translates, its signature, its
    blocks, and whether it touches memory."""
    with tempfile.TemporaryDirectory() as d:
        p = Path(d) / "m.ll"
        p.write_text(ll)
        r = subprocess.run([str(TOOL), str(p), "--report"], capture_output=True, text=True, check=False)
    rows = [x.split("\t") for x in r.stdout.splitlines() if "\t" in x]
    return {"rows": rows}


WIDTH = re.compile(r"i(\d+)")


def judge(step: dict, binding: Any) -> dict:
    """What stops tools/binding.py from binding this step, before any proof is written. An empty list means a
    certificate is worth attempting. The tool decides; this only saves running it where it can't say
    `bound`."""
    before, after = step["before"] or "", step["after"]
    blockers = []
    if not step["reproduced"]:
        comments = step["replay_differs_only_in_comments"]
        blockers.append("replay_mismatch_comments_only" if comments else "replay_mismatch")
    if binding.TRUSTED_PROMISES.search(after):
        blockers.append("trusted_promise")
    defined_after = [m.group(1) for m in binding.DEFINE.finditer(after)]
    defined_before = [m.group(1) for m in binding.DEFINE.finditer(before)]
    if len(defined_after) != 1 or defined_before != defined_after:
        blockers.append("not_one_function")
    shape: dict[str, Any] = {}
    if defined_after:
        fn = defined_after[0]
        params = binding.parameters(before, fn)
        if not all(re.search(r"\bnoundef\b", p) for p in params):
            blockers.append("undef_argument")
        rows = {side: ir_report(text)["rows"] for side, text in (("before", before), ("after", after))}
        for side, rs in rows.items():
            row = next((r for r in rs if len(r) > 1 and r[1] == fn), None)
            if row is None or row[0] != "ok":
                blockers.append(f"function_unsupported_{side}")
                continue
            if row[-1] != "pure":
                blockers.append(f"memory_{side}")
            sig = row[3]
            shape[side] = {"lean_name": row[2], "signature": sig, "blocks": int(row[4])}
        if "before" in shape and "after" in shape:
            sig = shape["before"]["signature"]
            args = sig.split(")->")[0].lstrip("(")
            widths = [int(m.group(1)) for m in WIDTH.finditer(args)] if args else []
            if not args or len(widths) != len(args.split(",")):
                blockers.append("arguments_not_integers")
            shape["function"], shape["widths"] = fn, widths
            if shape["before"]["blocks"] != 1 or shape["after"]["blocks"] != 1:
                blockers.append("no_certificate_template: more than one block, which needs AUTO-01")
    return {"blockers": sorted(set(blockers)), "shape": shape}


def case_name(path: Path) -> str:
    return path.stem


def capture_case(path: Path, cfg: dict, pin: dict, leaves: list[dict], binding: Any) -> dict:
    _, classes = inventory_index()
    name = case_name(path)
    out = EVIDENCE / name
    data = path.read_bytes()
    log: list[dict] = []
    record: dict[str, Any] = {
        "schema": "ir-lean.o1.capture/1",
        "level": LEVEL,
        "spec": cfg["spec"],
        "case": name,
        "host": host_key(),
        "opt_sha256": pin["opt"]["sha256"],
        "input_sha256": sha256_bytes(data),
    }
    target = binding.ir_target(data.decode(errors="replace"))
    if target != {"triple": cfg["mtriple"], "datalayout": cfg["datalayout"]}:
        record["status"] = "refused"
        record["reason"] = f"the input's target is {target}, not the pinned one"
        return record
    opt = pin["opt"]["path"]
    if sha256_file(Path(opt)) != pin["opt"]["sha256"]:
        sys.exit(f"{opt} doesn't hash as pinned")
    argv = binding.opt_argv(opt, cfg["spec"], cfg["mtriple"])
    timeout = cfg["budget"]["opt_timeout_s"]
    code1, o1, err1 = opt_run(argv, data, f"{name}: {cfg['spec']}", timeout, log)
    code2, o2, _ = opt_run(argv, data, f"{name}: {cfg['spec']} again", timeout, log)
    trace_argv = [*argv, "-debug-pass-manager", "-print-changed", "-print-module-scope"]
    code3, o3, trace = opt_run(trace_argv, data, f"{name}: {cfg['spec']} traced", timeout, log)
    if code1 != 0 or code2 != 0 or code3 != 0:
        record["status"] = "error"
        record["reason"] = f"opt failed: {err1[-300:]}"
        record["measurements"] = log
        return record
    found = attribute(parse_trace(trace), leaves, classes)
    src_code, src, _ = opt_run(
        binding.opt_argv(opt, "verify", cfg["mtriple"]), data, f"{name}: verify", timeout, log
    )
    record |= {
        "o1_sha256": sha256_bytes(o1),
        "deterministic": o1 == o2,
        "trace_output_matches": o3 == o1,
        "trace_start_is_source": src_code == 0 and found["start"] == src.decode(),
        "trace_final_is_output": found["final"] == o1.decode(),
        "analyses": found["analyses"],
        "positions_run": sorted({r["pos"] for r in found["runs"] if r["pos"]}, key=pos_key),
        "implicit_passes": sorted({r["name"] for r in found["runs"] if r["implicit"]}),
        "invocation_passes": found["invocation"],
    }
    out.mkdir(parents=True, exist_ok=True)
    steps_dir = out / "steps"
    if steps_dir.exists():
        shutil.rmtree(steps_dir)
    steps_dir.mkdir()
    (out / "input.ll").write_bytes(data)
    (out / "o1.ll").write_bytes(o1)
    (steps_dir / "00-start.ll").write_text(found["start"] or "")
    steps = []
    for k, s in enumerate(found["steps"], 1):
        before = (s["before"] or "").encode()
        reproduced, spec_used, comments_only = False, None, False
        for spec in s["replay"]:
            rargv = binding.opt_argv(opt, spec, cfg["mtriple"])
            code, got, _ = opt_run(rargv, before, f"{name}: step {k} replay {spec}", timeout, log)
            if code == 0 and got.decode() == s["after"]:
                reproduced, spec_used = True, spec
                break
            comments_only |= code == 0 and without_comments(got.decode()) == without_comments(s["after"])
        fname = f"{k:02d}-{re.sub(r'[^A-Za-z0-9_.-]', '_', s['name'])}.ll"
        (steps_dir / fname).write_text(s["after"])
        step = {
            "k": k,
            "pos": s["pos"],
            "name": s["name"],
            "class": s["class"],
            "unit": s["unit"],
            "family": s["family"],
            "implicit": s["implicit"],
            "again": s["again"],
            "spec": s["spec"],
            "replay_tried": s["replay"],
            "replay_spec": spec_used,
            "reproduced": reproduced,
            "replay_differs_only_in_comments": comments_only and not reproduced,
            "before_pos": s.get("before_pos"),
            "before_sha256": sha256_bytes(before),
            "after_sha256": sha256_bytes(s["after"].encode()),
            "after_file": f"steps/{fname}",
            "before": s["before"],
            "after": s["after"],
        }
        step |= judge(step, binding)
        del step["before"], step["after"]
        steps.append(step)
    record["steps"] = steps
    record["status"] = "captured"
    record["measurements"] = [summarize(m) for m in log]
    return record


PREDS = re.compile(r"\s+; preds = .*$", re.MULTILINE)


def without_comments(ll: str) -> str:
    """The IR without its `; preds =` comments and comment lines, which LLVM writes from use-list order. Text
    round trips don't keep that order, so a replay can differ in these and nothing else."""
    return "\n".join(x for x in PREDS.sub("", ll).splitlines() if not x.startswith(";"))


def pos_key(pos: str) -> list[int]:
    return [int(x) for x in pos.split(".")]


def summarize(m: dict) -> dict:
    keep = ("label", "outcome", "wall_s", "peak_process_mb", "peak_tree_mb", "limits")
    return {k: m[k] for k in keep} | {"command": [*m["command"][:1], "..."]}


def cmd_capture(args: argparse.Namespace) -> int:
    cfg = read_json(CONFIG)
    pin = host_pin()
    leaves = read_json(PIPELINE)["leaves"]
    binding = load_binding()
    cases = args.cases or sorted(CORPUS.glob("*.ll"))
    bad = 0
    for path in cases:
        record = capture_case(Path(path), cfg, pin, leaves, binding)
        write_json(EVIDENCE / record["case"] / "capture.json", record)
        ok = record["status"] == "captured" and all(
            record[k] for k in ("deterministic", "trace_output_matches", "trace_final_is_output")
        )
        bad += not ok
        n = len(record.get("steps", []))
        ready = sum(1 for s in record.get("steps", []) if not s["blockers"])
        print(f"{record['case']}: {record['status']}, {n} steps changed it, {ready} worth a certificate")
    return 1 if bad else 0


# ------------------------------------------------------------------------------------------------------------
# bind


def namespace_for(case: str, label: str) -> str:
    camel = "".join(w.capitalize() for w in re.split(r"[^A-Za-z0-9]+", case) if w)
    return f"O1{camel}{label.capitalize()}"


def certificate(ns: str, fn: str, widths: list[int], about: str) -> str:
    """A proof attempt for one straight-line function on each side. tools/binding.py decides whether it
    binds."""
    args = [f"a{i}" for i in range(len(widths))]
    binders = " ".join(f"({a} : IRLean.Val {w})" for a, w in zip(args, widths, strict=True))
    src, tgt = f"{ns}.Src.{fn}", f"{ns}.Tgt.{fn}"
    cases = " <;> ".join(f"cases {a}" for a in args)
    return f"""import {ns}.Src
import {ns}.Tgt

/-! Generated by campaign/o1/o1.py: {about}. A proof attempt, for a function that is one block on each side;
tools/binding.py decides whether it binds. -/

open IRLean

theorem {ns}.cert : {src} = {tgt} ∧
    ∀ {binders} (s : IRLean.ModelStop), {src} {" ".join(args)} ≠ some (.error (.model s)) := by
  refine ⟨?_, ?_⟩
  · funext {" ".join(args)}
    {cases} <;> simp only [{src}, {tgt}, noundef]
    all_goals (rw [run, run]; simp [{src}.step, {tgt}.step, llvm])
    all_goals bv_decide
  · intro {" ".join(args)} s
    {cases} <;> simp only [{src}, noundef]
    all_goals (try rw [run])
    all_goals simp [{src}.step, llvm]
"""


VERDICT_KEEP = (
    "status",
    "reason",
    "detail",
    "statement",
    "uncovered_changes",
    "memory_capped",
    "cache",
    "key",
)


def bind_job(job: dict, cfg: dict, cap_mb: float) -> dict:
    """Records one bundle and verifies it, and returns what tools/binding.py said, with what it cost."""
    bundle: Path = job["bundle"]
    if bundle.exists():
        shutil.rmtree(bundle)
    work = WORK / "bind" / job["case"] / job["label"]
    if work.exists():
        shutil.rmtree(work)
    work.mkdir(parents=True)
    input_ll = work / "input.ll"
    input_ll.write_text(job["input"])
    cert = work / "Cert.lean"
    cert.write_text(certificate(job["ns"], job["lean_name"], job["widths"], job["about"]))
    budget = cfg["budget"]
    record = subprocess.run(
        [
            *(sys.executable, str(BINDING), "record", "--input", str(input_ll), "--passes", job["passes"]),
            *("--mtriple", cfg["mtriple"], "--function", job["function"], "--certificate", str(cert)),
            *("--theorem", f"{job['ns']}.cert", "--namespace", job["ns"], "--out", str(bundle)),
        ],
        capture_output=True,
        text=True,
        check=False,
    )
    result: dict[str, Any] = {"label": job["label"], "passes": job["passes"], "namespace": job["ns"]}
    if record.returncode != 0:
        return result | {"status": "error", "reason": "record_failed", "detail": record.stderr[-600:]}
    while why := measure.too_busy(budget["min_available_mb"]):
        print(f"waiting: {why}", file=sys.stderr)
        time.sleep(30)
    with tempfile.TemporaryFile() as o:
        argv = [sys.executable, str(BINDING), "verify", str(bundle / "manifest.json")]
        argv += ["--memory", str(budget["lean_memory_mb"]), "--timeout", str(budget["step_timeout_s"])]
        rec = measure.run(
            argv,
            label=f"{job['case']}: {job['label']} verify",
            timeout=budget["step_timeout_s"] * 8,
            cap_mb=cap_mb,
            stdout=o,
            stderr=subprocess.DEVNULL,
        )
        o.seek(0)
        text = o.read().decode(errors="replace")
    rec["caps"] = [f"lean -M {budget['lean_memory_mb']}", f"tree RSS {cap_mb:.0f} MiB"]
    try:
        verdict: dict[str, Any] = json.loads(text)
    except json.JSONDecodeError:
        verdict = {"status": "error", "reason": "verdict_unreadable", "detail": text[-400:]}
    if rec["outcome"] in ("time_limit", "resource_limit"):
        # The measurement's own limit stopped the verifier: unknown, as tools/binding.py would say.
        verdict = {
            "status": "unknown",
            "reason": rec["outcome"],
            "detail": "campaign/o1/measure.py stopped it",
        }
    if verdict.get("status") not in STATUSES:
        verdict = {"status": "error", "reason": "verdict_unreadable", "detail": text[-400:]}
    kept = {k: verdict[k] for k in VERDICT_KEEP if k in verdict}
    checks: list[dict[str, Any]] = verdict.get("checks", [])
    kept["checks"] = [[c.get("name"), c.get("result")] for c in checks]
    return result | kept | {"measurement": rec}


def bind_jobs(case: str, capture: dict) -> list[dict]:
    jobs = []
    out = EVIDENCE / case
    for s in capture.get("steps", []):
        shape = s.get("shape", {})
        if s["blockers"] or "widths" not in shape:
            continue
        before = (out / "steps" / previous_file(capture, s["k"])).read_text()
        label = f"s{s['k']:02d}"
        jobs.append(
            {
                "case": case,
                "label": label,
                "ns": namespace_for(case, label),
                "input": before,
                "passes": s["replay_spec"],
                "function": shape["function"],
                "lean_name": shape["before"]["lean_name"],
                "widths": shape["widths"],
                "about": f"{case}, step {s['k']}, {s['spec']} at position {s['pos']} of default<O1>",
                "bundle": out / "bundles" / label,
                "step": s["k"],
            }
        )
    # The whole run as one claim, whatever its steps: tools/binding.py says whether it can judge it.
    first = next((s for s in capture.get("steps", []) if s.get("shape", {}).get("widths") is not None), None)
    if first is not None:
        shape = first["shape"]
        jobs.append(
            {
                "case": case,
                "label": "o1",
                "ns": namespace_for(case, "o1"),
                "input": (out / "input.ll").read_text(),
                "passes": capture["spec"],
                "function": shape["function"],
                "lean_name": shape["before"]["lean_name"],
                "widths": shape["widths"],
                "about": f"{case}, the whole {capture['spec']} run",
                "bundle": out / "bundles" / "o1",
                "step": None,
            }
        )
    return jobs


def previous_file(capture: dict, k: int) -> str:
    if k == 1:
        return "00-start.ll"
    prev = next(s for s in capture["steps"] if s["k"] == k - 1)
    return prev["after_file"].removeprefix("steps/")


def cmd_bind(args: argparse.Namespace) -> int:
    cfg = read_json(CONFIG)
    budget = cfg["budget"]
    workers = args.workers or budget["workers"]
    cap = budget["total_tree_mb"] / workers
    jobs = []
    for cap_path in sorted(EVIDENCE.glob("*/capture.json")):
        capture = read_json(cap_path)
        if args.case and capture["case"] not in args.case:
            continue
        jobs += bind_jobs(capture["case"], capture)
    print(f"{len(jobs)} bundles, {workers} at a time, each capped at {cap:.0f} MiB of RSS", file=sys.stderr)
    sources = sources_fingerprint()
    results: dict[str, list[dict]] = {}
    lines = []
    with (
        measure.heavy_lock("o1 bind", 3600),
        concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool,
    ):
        # The library and ir-lean, built from the sources the fingerprint names, so a verdict labeled with
        # them is about them. Both builds are incremental, and do nothing when they're up to date.
        for label, argv in (
            ("lake build", ["lake", "build"]),
            ("ninja", ["ninja", "-C", str(ROOT / "build")]),
        ):
            m = measure.run(argv, label=f"o1 bind: {label}", timeout=3600, cap_mb=budget["total_tree_mb"])
            m["workers"] = 1
            lines.append(json.dumps(m, sort_keys=True))
            if m["outcome"] != "ok":
                sys.exit(f"{label} failed, so nothing was bound: {m['outcome']}")
        futures = {pool.submit(bind_job, j, cfg, cap): j for j in jobs}
        for f in concurrent.futures.as_completed(futures):
            j = futures[f]
            r = f.result()
            r["step"] = j["step"]
            results.setdefault(j["case"], []).append(r)
            m = r.pop("measurement", None)
            if m is not None:
                m["workers"] = workers
                lines.append(json.dumps(m, sort_keys=True))
                r["cost"] = summarize(m)
            print(f"{j['case']} {j['label']}: {r['status']} {r.get('reason', '')}", file=sys.stderr)
    # A source that changed while they ran makes every verdict of this run stale.
    if sources_fingerprint() != sources:
        sources = "changed while bind ran"
    for case, rs in results.items():
        for r in rs:
            r["sources"] = sources
        write_json(EVIDENCE / case / "verdicts.json", sorted(rs, key=lambda r: r["label"]))
    MEASUREMENTS.mkdir(parents=True, exist_ok=True)
    with (MEASUREMENTS / f"{host_key()}.jsonl").open("a") as f:
        for line in lines:
            f.write(line + "\n")
    return 0


# ------------------------------------------------------------------------------------------------------------
# ledger

# What the analyses opt ran are, for what proving them means. All of them stay obligations: a heuristic's
# obligation is that no transform's correctness depends on it, and infrastructure's is that the pass manager
# hands each pass a result that's still true (PASS-05).
HEURISTIC = {
    "InlineAdvisorAnalysis",
    "OptimizationRemarkEmitterAnalysis",
    "ProfileSummaryAnalysis",
    "TargetIRAnalysis",
}


def analysis_kind(name: str) -> str:
    if "Proxy" in name or name in ("LastRunTrackingAnalysis", "ShouldNotRunFunctionPassesAnalysis"):
        return "infrastructure"
    if name in HEURISTIC:
        return "heuristic"
    return "fact"


def linked(case: dict, v: dict) -> bool:
    """A bundle is about this run only if its input and target IR are the captured IR, byte for byte."""
    manifest = EVIDENCE / case["case"] / "bundles" / v["label"] / "manifest.json"
    if not manifest.exists():
        return False
    art = read_json(manifest)["artifacts"]
    if v["step"] is None:
        want = (case.get("input_sha256"), case.get("o1_sha256"))
    else:
        s = next((s for s in case.get("steps", []) if s["k"] == v["step"]), None)
        if s is None:
            return False
        want = (s["before_sha256"], s["after_sha256"])
    return (art["input"]["sha256"], art["tgt_ir"]["sha256"]) == want


# The tracked files a verdict rests on: the checker, the model, the emitter, and the pins of Lean, LLVM and
# the toolchain. A verdict made with any of them different is stale, whatever it says.
SOURCES = [
    "tools/binding.py",
    "tools/binding_check.lean",
    "tests/check_axioms.lean",
    "IRLean.lean",
    "lean-toolchain",
    "lakefile.toml",
    "lake-manifest.json",
    "src/Emitter.cpp",
    "src/Emitter.h",
    "src/main.cpp",
    "tests/llvm/targets.toml",
    "flake.lock",
    "nix/shell.nix",
]


def sources_fingerprint() -> str:
    files = sorted({*SOURCES, *(str(p.relative_to(ROOT)) for p in (ROOT / "IRLean").rglob("*.lean"))})
    digest = hashlib.sha256()
    for f in files:
        p = ROOT / f
        digest.update(f"{f}\0{sha256_file(p) if p.exists() else 'missing'}\n".encode())
    return digest.hexdigest()


def standing(case: dict, v: dict, sources: str) -> str:
    """What a verdict counts as. Only `bound` is evidence: one tools/binding.py gave in a full replay, under
    these sources, about the captured IR."""
    status = v["status"] if v["status"] in STATUSES else "error"
    if status != "bound":
        return status
    if v.get("sources") != sources:
        return "bound_stale"
    if v.get("checks", [])[-1:] != [["unchanged", "pass"]]:
        return "bound_unreplayed"
    return "bound" if linked(case, v) else "bound_unlinked"


def derive_ledger(
    pipeline: dict, families: dict, captures: list[dict], verdicts: dict[str, list[dict]], sources: str
) -> dict:
    """The obligations default<O1> leaves, the evidence for each, and what blocks it. Only `bound` counts as
    evidence, and only as translation validation. `sources` is the fingerprint verdicts have to be made
    under to count."""
    leaves = pipeline["leaves"]
    fam = family_of(families)
    names = sorted({x["name"] for x in leaves} | {p for c in captures for p in c.get("implicit_passes", [])})
    passes: dict[str, dict] = {}
    for n in names:
        f = fam.get(n)
        passes[n] = {
            "family": f,
            "positions": [x["pos"] for x in leaves if x["name"] == n],
            "implicit": not any(x["name"] == n for x in leaves),
            "steps_changed": 0,
            "steps_bound": 0,
            "all-input": "open",
            "code-binding": "open",
            "composition": "open",
            "blocked_by": families["families"][f]["blocked_by"] if f else ["no family"],
        }
    extra = ("bound_stale", "bound_unreplayed", "bound_unlinked", "not_attempted")
    counts = dict.fromkeys((*STATUSES, *extra), 0)
    whole_counts: dict[str, int] = {}
    reasons: dict[str, int] = {}
    blockers: dict[str, int] = {}
    cases = {}
    gate: dict[str, int] = {}
    positions_run: set[str] = set()
    positions_changed: set[str] = set()
    analyses: dict[str, int] = {}
    for c in captures:
        name = c["case"]
        vs = {v["step"]: v for v in verdicts.get(name, []) if v["step"] is not None}
        whole = next((v for v in verdicts.get(name, []) if v["label"] == "o1"), None)
        if whole is not None:
            key = standing(c, whole, sources)
            key = f"{key}:{whole.get('reason')}" if key in STATUSES else key
            whole_counts[key] = whole_counts.get(key, 0) + 1
        positions_run |= set(c.get("positions_run", []))
        positions_changed |= {s["pos"] for s in c.get("steps", []) if s["pos"]}
        for a, k in c.get("analyses", {}).items():
            analyses[a] = analyses.get(a, 0) + k
        bound_steps, first_promise = 0, None
        for s in c.get("steps", []):
            p = passes.get(s["name"])
            if p is not None:
                p["steps_changed"] += 1
            v = vs.get(s["k"])
            if v is None:
                counts["not_attempted"] += 1
                for b in s["blockers"]:
                    key = b.split(":")[0]
                    blockers[key] = blockers.get(key, 0) + 1
            else:
                status = standing(c, v, sources)
                counts[status] += 1
                key = f"{status}:{v.get('reason')}"
                reasons[key] = reasons.get(key, 0) + 1
                if status == "bound":
                    bound_steps += 1
                    if p is not None:
                        p["steps_bound"] += 1
            if first_promise is None and "trusted_promise" in s["blockers"]:
                first_promise = s
        steps = c.get("steps", [])
        if first_promise is not None:
            later = sum(1 for s in steps if s["k"] >= first_promise["k"])
            key = first_promise["family"] or first_promise["name"]
            gate[key] = gate.get(key, 0) + later
        unbound = [s for s in steps if s["k"] not in vs or standing(c, vs[s["k"]], sources) != "bound"]
        if not steps:
            chain = "no step changed the module"
        elif not unbound:
            chain = "every step bound and linked: the run's input equals its output in IRLean, for this input"
        else:
            first = unbound[0]
            why = (vs.get(first["k"]) or {}).get("reason") or ",".join(
                b.split(":")[0] for b in first["blockers"]
            )
            chain = f"broken at step {first['k']} of {len(steps)}, {first['name']}: {why}"
        cases[name] = {
            "o1_sha256": c.get("o1_sha256"),
            "input_sha256": c.get("input_sha256"),
            "replayed_consistently": all(
                c.get(k) for k in ("deterministic", "trace_output_matches", "trace_final_is_output")
            ),
            "steps_changed": len(steps),
            "steps_bound": bound_steps,
            "chain_to_output": chain,
            "whole_run": {k: whole.get(k) for k in ("status", "reason")} if whole else "not attempted",
            "first_promise_step": (
                {"k": first_promise["k"], "pass": first_promise["name"], "pos": first_promise["pos"]}
                if first_promise
                else None
            ),
        }
    fam_rows = {}
    for f, info in families["families"].items():
        members = [n for n in names if passes[n]["family"] == f]
        fam_rows[f] = {
            "title": info["title"],
            "passes": len(members),
            "positions": sum(len(passes[n]["positions"]) for n in members),
            "steps_changed": sum(passes[n]["steps_changed"] for n in members),
            "steps_bound": sum(passes[n]["steps_bound"] for n in members),
            "later_steps_its_promises_block": gate.get(f, 0),
            "all_input_proved": 0,
            "blocked_by": info["blocked_by"],
        }
    priority = sorted(
        fam_rows,
        key=lambda f: (
            -fam_rows[f]["later_steps_its_promises_block"],
            -fam_rows[f]["steps_changed"],
            -fam_rows[f]["positions"],
            f,
        ),
    )
    return {
        "schema": "ir-lean.o1.ledger/1",
        "level": LEVEL,
        "spec": pipeline["spec"],
        "pipeline_sha256": pipeline["pipeline_sha256"],
        "evidence_sources": sources,
        "complete": False,
        "why_not_complete": [
            "No pass in default<O1> has an all-input proof, a binding to its C++, or a composition proof.",
            "Bound steps are translation validation of single runs on a finite corpus, and never count "
            "toward those.",
            "No independent verifier for all-input, code-binding or composition claims exists (BIND-03).",
        ],
        "denominators": {
            "positions": pipeline["positions"],
            "distinct_printed_passes": pipeline["distinct_passes"],
            "implicit_passes_seen": sorted(n for n in names if passes[n]["implicit"]),
            "passes": len(names),
            "families": len(families["families"]),
            "adaptors": len(pipeline["adaptors"]),
            "obligations": {
                "all-input": len(names),
                "code-binding": len(names),
                "composition_positions": pipeline["positions"],
                "composition_adaptors": len(pipeline["adaptors"]),
                "analysis-soundness": len(analyses),
            },
        },
        "discharged": {"all-input": 0, "code-binding": 0, "composition": 0, "analysis-soundness": 0},
        "lemmas": {
            "checked": 0,
            "instances_discharged_by_a_lemma": 0,
            "note": "Every bound step is its own certificate. A lemma counts only once it's kernel-checked "
            "under stated assumptions and a checked instantiation links it to a captured step's exact IR",
        },
        "corpus": {
            "cases": len(captures),
            "positions_run": len(positions_run),
            "positions_never_run": len([x for x in leaves if x["pos"] not in positions_run]),
            "positions_that_changed_ir": len(positions_changed),
            "steps": sum(len(c.get("steps", [])) for c in captures),
            "verdicts": counts,
            "verdict_reasons": dict(sorted(reasons.items())),
            "not_attempted_because": dict(sorted(blockers.items())),
            "whole_run_verdicts": dict(sorted(whole_counts.items())),
        },
        "analyses_seen": {
            "note": "Those this corpus made opt run: a lower bound on what default<O1> reads",
            "by_kind": {
                k: sorted(a for a in analyses if analysis_kind(a) == k)
                for k in ("fact", "heuristic", "infrastructure")
            },
        },
        "families": fam_rows,
        "priority": priority,
        "passes": passes,
        "cases": cases,
    }


def gather() -> tuple[list[dict], dict[str, list[dict]]]:
    captures = [read_json(p) for p in sorted(EVIDENCE.glob("*/capture.json"))]
    verdicts = {p.parent.name: read_json(p) for p in sorted(EVIDENCE.glob("*/verdicts.json"))}
    return captures, verdicts


def cmd_ledger(args: argparse.Namespace) -> int:
    captures, verdicts = gather()
    data = derive_ledger(read_json(PIPELINE), read_json(FAMILIES), captures, verdicts, sources_fingerprint())
    write_json(LEDGER, data)
    c = data["corpus"]
    print(f"{LEDGER}: {c['steps']} steps on {c['cases']} cases, verdicts {c['verdicts']}; complete: false")
    return 0


# ------------------------------------------------------------------------------------------------------------
# check


DOC = ROOT / "docs" / "o1-campaign.md"
SUMMARY = re.compile(r"<!-- o1-summary: (\{.*\}) -->")


def summary(ledger: dict) -> dict:
    """The numbers docs/o1-campaign.md states, so the doc can't drift from the ledger."""
    d, c = ledger["denominators"], ledger["corpus"]
    return {
        "level": ledger["level"],
        "positions": d["positions"],
        "passes": d["passes"],
        "families": d["families"],
        "adaptors": d["adaptors"],
        "cases": c["cases"],
        "steps": c["steps"],
        "verdicts": c["verdicts"],
        "whole_run": c["whole_run_verdicts"],
        "discharged": sum(ledger["discharged"].values()),
        "complete": ledger["complete"],
        "evidence_sources": ledger["evidence_sources"],
    }


def check_consistency(allow_stale: bool = False) -> list[str]:
    """What's wrong with the committed files, without running LLVM or Lean. Evidence verified under sources
    other than these is stale, and a problem unless `allow_stale`."""
    problems = []
    cfg = read_json(CONFIG)
    families = read_json(FAMILIES)
    try:
        fam = family_of(families)
    except ValueError as e:
        return [str(e)]
    pin = read_json(PIN)
    for host, p in pin["hosts"].items():
        inventory = read_json(INVENTORY)["pipelines"]["opt"][cfg["spec"]]["pipeline"]
        if p["pipeline"]["text"] != inventory:
            problems.append(f"{host}'s pipeline isn't the inventory's {cfg['spec']}")
        if p["llvm"]["commit"] != tomllib.loads(TARGETS.read_text())["project"]["commit"]:
            problems.append(f"{host}'s LLVM commit isn't the repo's pin")
    pipeline = read_json(PIPELINE)
    any_pin = next(iter(pin["hosts"].values()))
    if pipeline != derive_pipeline(any_pin["pipeline"]["text"]):
        problems.append("pipeline.json isn't what `pipeline` derives from the pin")
    captures, verdicts = gather()
    implicit = {p for c in captures for p in c.get("implicit_passes", [])}
    for n in sorted({x["name"] for x in pipeline["leaves"]} | implicit):
        if n not in fam:
            problems.append(f"{n} has no family")
    for c in captures:
        if c.get("level") != LEVEL or c.get("spec") != cfg["spec"]:
            problems.append(f"{c['case']} isn't a {cfg['spec']} capture")
        for s in c.get("steps", []):
            f = EVIDENCE / c["case"] / s["after_file"]
            if not f.exists() or sha256_file(f) != s["after_sha256"]:
                problems.append(f"{c['case']} step {s['k']}'s IR isn't what was captured")
    by_case = {c["case"]: c for c in captures}
    for case, vs in verdicts.items():
        for v in vs:
            if v["status"] == "bound" and (case not in by_case or not linked(by_case[case], v)):
                problems.append(f"{case} {v['label']} is bound to IR that isn't the captured run's")
            if v["status"] not in STATUSES:
                problems.append(f"{case} {v['label']} has status {v['status']}")
            if v["status"] == "bound" and v.get("checks", [])[-1:] != [["unchanged", "pass"]]:
                problems.append(f"{case} {v['label']} is bound without every check")
            manifest = EVIDENCE / case / "bundles" / v["label"] / "manifest.json"
            if v["status"] == "bound" and not manifest.exists():
                problems.append(f"{case} {v['label']} is bound with no bundle to replay")
    ledger = read_json(LEDGER)
    # Against the sources the ledger names, so another lane's change to the model doesn't break this check.
    # `cmd_check` says when they aren't the current ones, and `ledger` then counts nothing but stale.
    if ledger != derive_ledger(pipeline, families, captures, verdicts, ledger.get("evidence_sources", "")):
        problems.append("ledger.json isn't what `ledger` derives from the evidence")
    if ledger.get("complete") is not False:
        problems.append("ledger.json says O1 is complete")
    if not allow_stale and ledger.get("evidence_sources") != sources_fingerprint():
        problems.append(
            "ledger.json counts evidence verified under other sources, which is stale here: "
            "run `bind`, then `ledger`"
        )
    stated = SUMMARY.search(DOC.read_text()) if DOC.exists() else None
    if stated is None or json.loads(stated.group(1)) != summary(ledger):
        problems.append(f"{DOC.name}'s o1-summary isn't the ledger's: {json.dumps(summary(ledger))}")
    return problems


def cmd_check(args: argparse.Namespace) -> int:
    problems = check_consistency(args.allow_stale)
    for p in problems:
        print(p, file=sys.stderr)
    if not problems:
        print("campaign/o1 is consistent; O1 is not complete")
    recorded = read_json(LEDGER).get("evidence_sources")
    if args.allow_stale and recorded != sources_fingerprint():
        print(f"stale: ledger.json's counts hold only for sources {recorded}", file=sys.stderr)
    return 1 if problems else 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("pin")
    p.add_argument("--check", action="store_true")
    sub.add_parser("pipeline")
    c = sub.add_parser("capture")
    c.add_argument("cases", nargs="*", type=Path)
    b = sub.add_parser("bind")
    b.add_argument("--case", action="append")
    b.add_argument("--workers", type=int)
    sub.add_parser("ledger")
    k = sub.add_parser("check")
    k.add_argument(
        "--allow-stale",
        action="store_true",
        help="check the files agree, but don't fail when the evidence was verified under other sources",
    )
    args = ap.parse_args()
    with contextlib.suppress(KeyboardInterrupt):
        return {
            "pin": cmd_pin,
            "pipeline": cmd_pipeline,
            "capture": cmd_capture,
            "bind": cmd_bind,
            "ledger": cmd_ledger,
            "check": cmd_check,
        }[args.cmd](args)
    return 130


if __name__ == "__main__":
    sys.exit(main())
