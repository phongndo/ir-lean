#!/usr/bin/env python3
"""The results board, S8: every proved win on the kernel corpus, labeled by tier, with its measured speedup,
and what doesn't count and why. docs/board.md is this script's output, and nothing else writes it.

An entry is a record in bench/kernels/board/, one per rewrite, `ir-lean.board.win/1`. An entry that counts
toward S3's bar has to be everything docs/kernels.md's "What a win is" asks, and `check` refuses it otherwise:

- on the fixed corpus: the manifest is fixed, its project is approved, and it was found after the lock;
- proved: its Lean modules are in the repo, a test registered in CMakeLists.txt names each, they name each
  of its functions, and `proof.ir` gives the source and target IR the proof is about, which the test names;
- reviewed: a second agent's review of the statement, and a must-break mutant, as decision 11 asks;
- measured: comparisons in the repo, each a measurement of its own, made by bench/kernels/harness.py with
  the protocol's rule, each measurably faster, against the -O3 baseline, and against the project's own
  level where that isn't -O3, with every other workload of the project measured and none slower;
- the rewrite measured: each comparison's candidate, by the build records beside its plan, is built from
  the corpus's pin with its flags and clang, rewrites the entry's unit and declares its functions, from the
  proof's source IR to its target, and is given as that IR, which the harness compiles with the pinned llc:
  a candidate given as an object can be a control or an exploration, and never a win;
- labeled: what's proved, what it rests on, the source IR, and how it was found.

No two entries are one rewrite, or cite one comparison. Every comparison the board cites, and every harness
control in bench/kernels/results/controls/, is worked out again from its sessions, its plan and the build
records beside it, and has to give all of what's recorded: what it compares, at what level, and whether
it's a control, not only its statistic and verdict.

usage: bench/kernels/board.py write    write docs/board.md from the records
       bench/kernels/board.py check    check every record, and that docs/board.md is what `write` gives
"""

from __future__ import annotations

import contextlib
import os
import re
import sys
from pathlib import Path
from typing import Any

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.append(str(ROOT / "tools"))
sys.path.append(str(HERE))
import harness  # noqa: E402
import kernels  # noqa: E402
import protocol  # noqa: E402
from irlean import hashing, schemas  # noqa: E402

ENTRIES = HERE / "board"
CONTROLS = HERE / "results" / "controls"
PAGE = ROOT / "docs" / "board.md"
CMAKE = ROOT / "CMakeLists.txt"
# S3's bar, decision 8 of 2026-11-09 after #103.
BAR_WINS = 10
BAR_PROJECTS = 3
# The four labels of "What a win is", and the values each takes. "by hand" is for what doesn't count.
LABELS = {
    "proved": ("slice", "whole function"),
    "axioms": ("standard", "standard and bv_decide"),
    "source_ir": ("as built", "relaxed"),
    "found_by": ("rule search", "rule written for its site", "agent proposer", "by hand"),
}


def show(path: Path) -> str:
    """A path as a message names it: from the repo's root if it's in the repo."""
    return str(path.relative_to(ROOT)) if path.is_relative_to(ROOT) else str(path)


def entries() -> list[tuple[Path, dict[str, Any]]]:
    return [(p, schemas.read(p, schemas.BOARD_WIN)) for p in sorted(ENTRIES.glob("*.json"))]


def controls() -> list[Path]:
    return sorted(CONTROLS.rglob("*.comparison.json"))


def recompute(path: Path) -> list[str]:
    """What's wrong with a comparison record: its sessions missing or changed, or any of it, the builds and
    level it compares, whether it's a control, its statistic or its verdict, that its sessions, its plan and
    the build records beside the plan don't give. The workloads it has to account for are the project's, from
    its configuration, not the ones it lists."""
    stored = schemas.read(path, schemas.KERNELS_COMPARISON)
    where = path.parent
    sessions = {}
    for p in sorted(where.glob("*.json")):
        with contextlib.suppress(schemas.SchemaError):
            record = schemas.read(p, schemas.KERNELS_SESSION)
            record["_sha256"] = hashing.sha256_file(p)
            sessions[record["_sha256"]] = record
    main = [sessions.get(s["sha256"]) for s in stored["sessions"]]
    if not main or any(s is None for s in main):
        return [f"{show(path)}: a session it cites isn't beside it, as it was"]
    others: dict[str, list[dict[str, Any]]] = {}
    for name, summary in stored["others"].items():
        if any(sha not in sessions for sha in summary["sessions"]):
            return [f"{show(path)}: a session of {name} it cites isn't beside it, as it was"]
        others[name] = [sessions[sha] for sha in summary["sessions"]]
    plans = harness.read_plans(where)
    found = [s for s in main if s is not None]
    if twice := harness.recorded_twice([*found, *(s for x in others.values() for s in x)], where):
        return [f"{show(path)}: {p}" for p in twice]
    names = harness.required_workloads(plans.get(found[0]["plan_sha256"]), stored["project"])
    try:
        again = harness.compare(found, others, names, protocol.Rule(**stored["rule"]), plans)
    except harness.Refused as error:
        return [f"{show(path)}: {error}"]
    return [
        f"{show(path)}: its {k} isn't what its sessions and plan give"
        for k in sorted(again.keys() | stored.keys())
        if again.get(k) != stored.get(k)
    ]


def plan_of(path: Path) -> dict[str, Any] | None:
    """A comparison's plan, with its build records, from beside it."""
    return harness.read_plans(path.parent).get(schemas.read(path, schemas.KERNELS_COMPARISON)["plan_sha256"])


def test_text(name: str) -> str | None:
    """A test registered in CMakeLists.txt: its command, and the text of each file in the repo it runs, or
    None if there's no test of that name."""
    m = re.search(rf"add_test\(\s*NAME\s+{re.escape(name)}\s+COMMAND\s+([^)]*)\)", CMAKE.read_text())
    if m is None:
        return None
    text = m[1]
    for arg in re.findall(r"\$\{CMAKE_SOURCE_DIR\}/(\S+)", m[1]):
        if (ROOT / arg).is_file():
            text += "\n" + (ROOT / arg).read_text(errors="replace")
    return text


def built(
    what: str, e: dict[str, Any], project: dict[str, Any], corpus: dict[str, Any], plan: Any
) -> list[str]:
    """How a comparison's builds, by the records beside its plan, aren't this entry's rewrite: the baseline
    and the candidate built from the corpus's pin with its flags and toolchain by this harness, and the
    candidate rewriting the entry's unit, declaring its functions, from the proof's source IR to its
    target."""
    builds = (plan or {}).get("_builds") or {}
    base, cand = builds.get("baseline"), builds.get("candidate")
    if base is None or cand is None:
        return [f"{what}: its plan's build records aren't beside it"]
    out = []
    version = corpus["llvm_tag"].removeprefix("llvmorg-")
    for role, r in (("baseline", base), ("candidate", cand)):
        if r["schema"] != schemas.KERNELS_BUILD:
            out.append(f"{what}: its {role} was built by an earlier harness, {r['schema']}")
        pin = r.get("pin") or {}
        if (pin.get("rev"), pin.get("nix_hash")) != (project["rev"], project["nix_hash"]):
            out.append(f"{what}: its {role} isn't built from {e['project']} at the corpus's pin")
        if r.get("flags") != corpus.get("flags"):
            out.append(f"{what}: its {role} isn't built with the corpus's flags")
        tools = r.get("tools") or {}
        if f"clang version {version}" not in ((tools.get("clang") or {}).get("version") or "") or (
            f"LLVM version {version}" not in ((tools.get("llc") or {}).get("version") or "")
        ):
            out.append(f"{what}: its {role} isn't built with the corpus's clang and llc, {version}")
    if base["variant"] != "baseline" or base["control"] is not None:
        out.append(f"{what}: its baseline isn't the baseline build")
    info = cand.get("candidate") or {}
    if cand["control"] is not None or info.get("form") not in ("ir", "object"):
        out.append(f"{what}: its candidate isn't a rewrite")
    elif info["form"] == "object":
        out.append(
            f"{what}: its candidate is an object, and only a rewrite given as IR, which the harness compiles "
            "with the pinned llc, can count: nothing proves an object is its proof's target compiled"
        )
    if info.get("unit") != e.get("unit"):
        out.append(
            f"{what}: its candidate rewrites {info.get('unit')!r}, and the entry's unit is {e.get('unit')!r}"
        )
    if info.get("declared") != sorted(e.get("functions") or []):
        out.append(
            f"{what}: its candidate declares {info.get('declared')}, and the entry's functions are "
            f"{sorted(e.get('functions') or [])}"
        )
    sources = {o.get("ir_sha256") for o in info.get("objects") or []}
    pairs = [
        (ROOT / x.get("source", ""), ROOT / x.get("target", ""))
        for x in (e.get("proof") or {}).get("ir") or []
    ]
    if not any(
        s.is_file()
        and t.is_file()
        and hashing.sha256_file(s) in sources
        and hashing.sha256_file(t) == info.get("input_sha256")
        for s, t in pairs
    ):
        out.append(
            f"{what}: its proof isn't about its candidate: no pair in proof.ir has the unit's IR as built as "
            f"its source and the candidate's input, {info.get('input_sha256')}, as its target"
        )
    return out


def duplicates(found: list[tuple[Path, dict[str, Any]]]) -> list[str]:
    """Entries that are one rewrite, by project, unit and functions, or that cite one comparison."""
    out = []
    seen: dict[Any, Path] = {}
    for path, e in found:
        keys: list[Any] = [
            ("the rewrite", e.get("project"), e.get("unit"), tuple(sorted(e.get("functions") or [])))
        ]
        for m in (e.get("measured") or {}).get("comparisons", []):
            keys += [("the comparison", m.get("path")), ("the comparison", m.get("sha256"))]
        for key in dict.fromkeys(keys):
            if key in seen:
                out.append(
                    f"{show(path)}: {key[0]} {key[1:]} is {show(seen[key])}'s too: one rewrite, one entry"
                )
            else:
                seen[key] = path
    return out


def problems(path: Path, e: dict[str, Any], manifest: dict[str, Any]) -> list[str]:
    """What's wrong with an entry, or nothing."""
    label = f"{show(path)}"
    out = []
    if e.get("id") != path.stem:
        out.append(f"{label}: its id isn't its file's name")
    project = manifest["project"].get(e.get("project"))
    if project is None:
        return [*out, f"{label}: the manifest has no project {e.get('project')!r}"]
    for key, values in LABELS.items():
        if e.get("labels", {}).get(key) not in values:
            out.append(
                f"{label}: label {key} is {e.get('labels', {}).get(key)!r}, not one of {', '.join(values)}"
            )
    proof = e.get("proof") or {}
    test = proof.get("test")
    command = test_text(test) if isinstance(test, str) else None
    if command is None:
        out.append(f"{label}: no test named {test!r} is registered in CMakeLists.txt to check its proof")
    modules = proof.get("modules") or []
    if not modules:
        out.append(f"{label}: its proof names no module")
    for module in modules:
        if not (ROOT / module).is_file() or not module.endswith(".lean"):
            out.append(f"{label}: its proof's module {module} isn't a Lean module in the repo")
        elif command is not None and Path(module).name not in command:
            out.append(f"{label}: its proof's test, {test}, doesn't name its module {module}")
    if not e.get("functions"):
        out.append(f"{label}: it names no function")
    if not e["counts"]:
        if not e.get("why_not"):
            out.append(f"{label}: an entry that doesn't count says why")
        return out
    # From here on, an entry that counts toward the bar.
    corpus = manifest["corpus"]
    if corpus["state"] != "fixed":
        out.append(f"{label}: the corpus is {corpus['state']}, not fixed, so no win counts yet")
    if e["project"] not in corpus.get("approved", []):
        out.append(f"{label}: {e['project']} isn't an approved project")
    lock = manifest.get("lock", {})
    if not e.get("found", {}).get("after_lock") or e.get("found", {}).get("on", "") < lock.get(
        "approved_on", "9"
    ):
        out.append(f"{label}: it wasn't found after the corpus was fixed")
    if e["labels"]["found_by"] == "by hand":
        out.append(f"{label}: found by hand isn't one of decision 8's ways a win is found")
    review = e.get("review") or {}
    if not review.get("statement") or not review.get("mutant"):
        out.append(f"{label}: it needs a second agent's review of its statement and a must-break mutant")
    # The proof is about these functions, from this source IR to this target, which its test reads.
    text = "".join((ROOT / m).read_text(errors="replace") for m in modules if (ROOT / m).is_file())
    if unnamed := [f for f in e.get("functions") or [] if f not in text]:
        out.append(f"{label}: its proof's modules don't name {unnamed}")
    if not proof.get("ir"):
        out.append(f"{label}: its proof gives no source and target IR, in proof.ir")
    for pair in proof.get("ir") or []:
        for side in ("source", "target"):
            where = ROOT / str(pair.get(side, ""))
            if not where.is_file():
                out.append(f"{label}: its proof's {side} IR {pair.get(side)} isn't in the repo")
            elif command is not None and where.name not in command:
                out.append(f"{label}: its proof's test, {test}, doesn't name its {side} IR {pair.get(side)}")
    levels = set()
    plans_seen: set[str] = set()
    measured = e.get("measured", {}).get("comparisons", [])
    if not measured:
        out.append(f"{label}: it has no comparison")
    for m in measured:
        where = ROOT / m["path"]
        if not where.is_file() or hashing.sha256_file(where) != m["sha256"]:
            out.append(f"{label}: {m['path']} isn't in the repo as it was")
            continue
        c = schemas.read(where, schemas.KERNELS_COMPARISON)
        out += recompute(where)
        what = f"{label}: {m['path']}"
        if c["plan_sha256"] in plans_seen:
            out.append(f"{what} is the measurement another of its comparisons is")
        plans_seen.add(c["plan_sha256"])
        out += built(what, e, project, corpus, plan_of(where))
        if c["project"] != e["project"] or c["control"] is not None:
            out.append(f"{what} is a control, or another project's")
        if c["rule"] != protocol.PROTOCOL.as_record() or not c["by_the_protocol"]:
            out.append(f"{what} isn't by the protocol: {'; '.join(c['protocol_problems']) or c['rule']}")
        if c["verdict"] != protocol.FASTER:
            out.append(f"{what} is {c['verdict']}, not measurably faster")
        if (c.get("baseline") or {}).get("variant") != "baseline":
            out.append(f"{what} isn't against the baseline")
        levels.add(c.get("opt"))
    want = {harness.CORPUS_OPT} | (
        {harness.OWN_OPT} if project["project_opt"] != harness.CORPUS_OPT else set()
    )
    if measured and not want <= levels:
        out.append(f"{label}: it's measured against {sorted(map(str, levels))}, and needs {sorted(want)}")
    return out


def check_all() -> list[str]:
    manifest = kernels.load()
    out = []
    found = entries()
    for path, e in found:
        out += problems(path, e, manifest)
    out += duplicates(found)
    for path in controls():
        out += recompute(path)
        c = schemas.read(path, schemas.KERNELS_COMPARISON)
        if c["control"] is None:
            out.append(f"{show(path)}: it's among the controls, and isn't one")
    return out


# ------------------------------------------------------------------------------------------------------------
# The page

HEAD = """\
# The results board

Every proved win on [the kernel corpus](kernels.md), labeled by tier, with its measured speedup, and what
doesn't count and why. It's S8 in the [roadmap](roadmap.md), the headline of decision 6 after #103.

This page is generated: `nix develop -c bench/kernels/board.py write` writes it from the records in
[`bench/kernels/board/`](../bench/kernels/board) and the harness's controls in
[`bench/kernels/results/controls/`](../bench/kernels/results/controls), and the `board` test fails if it isn't
what that gives. Don't edit it by hand.
"""

WINS = """\
## Wins

A win is one rewrite, proved, reviewed and measurably faster on a workload of its project, found on the
fixed corpus after its lock: [what a win is](kernels.md#what-a-win-is). Each carries four labels, and every
combination counts toward the bar.
"""

WINS_TABLE = [
    "| Project | Functions | Proved | Rests on | Source IR | Found by | Proof | Workload and baseline "
    "| Speedup, median [95% interval] | Sessions, pairs |",
    "| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |",
]

UNCOUNTED = """\
## Not counting

Proved rewrites on the corpus's projects that don't count toward the bar, each with why.

| Project | Functions | Proved | Rests on | Source IR | Found by | Proof | Measured | Why it doesn't count |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
"""

CONTROLS_HEAD = """\
## Harness controls

Checks on [the harness](kernels.md#the-harness), not on any rewrite, and never wins: a candidate the same as
the baseline has to come out inconclusive, one known slower slower, and one known faster faster. Each was
worked out again from its sessions when this page was written. A ratio above 1 is the candidate faster.
"""

CONTROLS_TABLE = [
    "| Run | Project | Workload and baseline | Control | Baseline against candidate | Verdict "
    "| Ratio, median [95% interval] | Sessions, pairs | Load average, each session's median | CPUs |",
    "| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |",
]

HOW = """\
## How a win gets here

1. The rule search finds a rewrite on the fixed corpus, and Lean proves it, in a module a test checks in CI.
2. [`bench/kernels/harness.py`](../bench/kernels/harness.py) builds the project's baseline and the candidate,
   and checks before timing that they differ only in the rewritten functions, that `llc` on the unchanged IR
   gives the baseline's machine code, and that each workload's output or check is the baseline's.
3. A plan is written down, then its confirmation sessions run, and `harness.py compare` reads them by
   [the rule](kernels.md#measurably-faster), against `-O3`, and against the project's own level where that's
   `-O2`, with every other workload of the project measured.
4. An entry in `bench/kernels/board/` cites the comparisons, the proof, with the source and target IR it's
   about, and the review, and `bench/kernels/board.py check` refuses it unless all of that holds, and the
   candidate each comparison measured is that rewrite, of that IR, built from the corpus's pin.
5. Only a rewrite given to the harness as IR, which it compiles with the pinned `llc`, can count. A candidate
   given as an object can be a control or an exploration, and never a win: the proof is about IR, and nothing
   proves an object is that IR compiled.
"""


def cell(text: Any) -> str:
    return str(text).replace("|", "\\|").replace("\n", " ")


def row(*cells: Any) -> str:
    return "| " + " | ".join(cell(c) for c in cells) + " |"


def speed(c: dict[str, Any]) -> str:
    p = c["pooled"]
    return f"{p['median']:.3f} [{p['interval'][0]:.3f}, {p['interval'][1]:.3f}]"


def link(path: str | Path) -> str:
    """A path in the repo, as the page links it."""
    return os.path.relpath(ROOT / path, PAGE.parent)


def proofs(e: dict[str, Any]) -> str:
    return ", ".join(f"[`{Path(x).name}`]({link(x)})" for x in e["proof"]["modules"])


def render() -> str:
    manifest = kernels.load()
    corpus = manifest["corpus"]
    all_entries = [e for _, e in entries()]
    wins = [e for e in all_entries if e["counts"]]
    projects = sorted({e["project"] for e in wins})
    if corpus["state"] != "fixed":
        standing = (
            f"The corpus is {corpus['state']}, not fixed, so no win can count yet: decision 7 waits for "
            "libsodium's bulk-encryption driver, and then the manifest's `[lock]`."
        )
    else:
        standing = f"The corpus was fixed on {manifest['lock']['approved_on']}."
    lines = [
        HEAD,
        f"**{len(wins)} wins from {len(projects)} projects,** against S3's bar of {BAR_WINS} from "
        f"{BAR_PROJECTS}.",
        standing,
        "",
        WINS,
    ]
    if not wins:
        lines += ["None yet.", ""]
    else:
        lines += WINS_TABLE
        for e in wins:
            for m in e["measured"]["comparisons"]:
                c = schemas.read(ROOT / m["path"], schemas.KERNELS_COMPARISON)
                lines.append(
                    row(
                        e["project"],
                        ", ".join(f"`{f}`" for f in e["functions"]),
                        e["labels"]["proved"],
                        e["labels"]["axioms"],
                        e["labels"]["source_ir"],
                        e["labels"]["found_by"],
                        proofs(e),
                        f"{c['workload']}, {c['opt']}",
                        speed(c),
                        f"{len(c['sessions'])}, {c['pooled']['pairs']}",
                    )
                )
        lines.append("")
    lines.append(UNCOUNTED.rstrip("\n"))
    for e in all_entries:
        if not e["counts"]:
            lines.append(
                row(
                    f"[{e['project']}]({link(e['doc'])})" if e.get("doc") else e["project"],
                    ", ".join(f"`{f}`" for f in e["functions"]),
                    e["labels"]["proved"],
                    e["labels"]["axioms"],
                    e["labels"]["source_ir"],
                    e["labels"]["found_by"],
                    proofs(e),
                    e["measured"]["summary"],
                    e["why_not"],
                )
            )
    lines += ["", CONTROLS_HEAD]
    rows = []
    for path in controls():
        c = schemas.read(path, schemas.KERNELS_COMPARISON)
        baseline = (c.get("baseline") or {}).get("variant")
        candidate = (c.get("candidate") or {}).get("variant")
        rows.append(
            row(
                f"[{path.parent.parent.name}]({link(path.parent.relative_to(ROOT))})",
                c["project"],
                f"{c['workload']}, {c['opt']}",
                c["control"],
                f"{baseline} against {candidate}",
                f"**{c['verdict']}**",
                speed(c),
                f"{len(c['sessions'])}, {c['pooled']['pairs']}",
                ", ".join(f"{s['load']['median']:.1f}" for s in c["sessions"]),
                ", ".join(map(str, sorted({cpu for s in c["sessions"] for cpu in s["cpus"]}))),
            )
        )
    lines += [*CONTROLS_TABLE, *rows] if rows else ["None recorded."]
    lines += ["", HOW]
    return "\n".join(lines)


def main(argv: list[str]) -> int:
    if argv not in (["write"], ["check"]):
        print(__doc__, file=sys.stderr)
        return 2
    found = check_all()
    for p in found:
        print(f"FAIL {p}")
    page = render()
    if argv == ["write"]:
        if found:
            return 1
        PAGE.write_text(page)
        print(f"ok   wrote {PAGE.relative_to(ROOT)}")
        return 0
    if PAGE.read_text() != page:
        print(f"FAIL {PAGE.relative_to(ROOT)} isn't what `bench/kernels/board.py write` gives: run it")
        return 1
    if not found:
        print(
            f"ok   {len(entries())} entries and {len(controls())} controls check, and "
            f"{PAGE.relative_to(ROOT)} is current"
        )
    return 1 if found else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
