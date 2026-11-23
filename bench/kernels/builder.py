#!/usr/bin/env python3
"""The builder of a kernel corpus variant's derivation, bench/kernels/variants.nix. docs/kernels.md.

It runs the plan Nix resolved from the manifest, in place in the derivation's output, and writes down what it
saw, as `evidence/evidence.json`: each known-answers check's commands and how each ended, whether the check's
result was there before it ran, and the result's and the expected file's SHA-256; each workload's run, its
environment, its words, how it ended and its output's SHA-256; each object the compiler made from the table's
IR, and each it compiled from one of the manifest's units.

It decides nothing. Each step of
the build, configure, make and each workload's build, is written down too, and the first that fails ends what
runs, not the builder: so a build that failed has evidence, which says so, and a store path, which nothing
measures.

usage: builder.py PLAN.json, with `out` and `TMPDIR` set, as a derivation's builder has them
"""

from __future__ import annotations

import json
import os
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(ROOT / "tools"))
from irlean import hashing, proc, schemas  # noqa: E402

# The seconds a command of the build, of a check, and a workload's run may take.
BUILD_SECONDS, CHECK_SECONDS, RUN_SECONDS = 3600, 1800, 1800


def sha256_of(path: Path) -> str | None:
    """The file's SHA-256, or None if there's no such file."""
    return hashing.sha256_file(path) if path.is_file() else None


def size_of(path: Path) -> int | None:
    """The file's size, or None if there's no such file."""
    return path.stat().st_size if path.is_file() else None


def ended(ran: proc.Ran) -> dict[str, Any]:
    """How a command ended, as the evidence has it."""
    return {"argv": [str(a) for a in ran.argv], "exit": ran.exit, "limit": ran.limit}


def written(directory: Path) -> dict[str, str]:
    """What the compiler wrote down in `directory`, a file for each object: the object, and what it's from."""
    found = {}
    for record in sorted(directory.iterdir()):
        key, value = record.read_text().split("\n")[:2]
        found[key] = value
    return found


def main(plan_path: Path) -> int:
    plan = json.loads(plan_path.read_text())
    out = Path(os.environ["out"])  # noqa: SIM112, a derivation's builder is given `out`
    work = Path(os.environ["TMPDIR"]) / "kernels-plan"
    for name in ("replace", "replaced", "compiled"):
        (work / name).mkdir(parents=True)
    for key, ir in plan["replace"].items():
        link = work / "replace" / key
        link.parent.mkdir(parents=True, exist_ok=True)
        link.symlink_to(ir)
    (work / "units").write_text("".join(unit + "\n" for unit in plan["units"]))
    logs = out / "logs"
    logs.mkdir()
    env = {**os.environ, "KERNELS_OUT": str(out), "KERNELS_PLAN": str(work), "CC": plan["cc"]}
    count = 0

    def logged(argv: list[str], seconds: int, more: dict[str, str] | None = None) -> proc.Ran:
        nonlocal count
        count += 1
        log = logs / f"{count:03}.log"
        return proc.run(
            argv, timeout=seconds, cwd=out, env={**env, **(more or {})}, stdout=log, stderr=proc.STDOUT
        )

    # The project's make takes its jobs from MAKEFLAGS, so its words are the plan's.
    jobs = {"MAKEFLAGS": f"-j{os.environ.get('NIX_BUILD_CORES', '1')}"}
    steps = [(plan["configure"], None), (["make"], jobs)]
    steps += [(argv, None) for workload in plan["workloads"] for argv in workload["build"]]
    built = []
    for argv, more in steps:
        built.append(ended(logged(argv, BUILD_SECONDS, more)))
        if built[-1]["exit"] != 0 or built[-1]["limit"] is not None:
            break
    record: dict[str, Any] = {
        "schema": schemas.KERNELS_EVIDENCE,
        "out": str(out),
        "build": built,
        "replaced": {key: hashing.sha256_file(Path(ir)) for key, ir in written(work / "replaced").items()},
        "compiled": written(work / "compiled"),
        "checks": [],
        "runs": [],
    }
    whole = len(built) == len(steps) and all(b["exit"] == 0 and b["limit"] is None for b in built)
    for workload in plan["workloads"] if whole else []:
        for check in workload["checks"]:
            if check["kind"] != "known-answers":
                continue
            result = Path(check["result"])
            before = result.exists()
            result.unlink(missing_ok=True)
            commands = [ended(logged(argv, CHECK_SECONDS, plan["check_env"])) for argv in check["run"]]
            record["checks"].append(
                {
                    "workload": workload["name"],
                    "commands": commands,
                    "expected": check["expected"],
                    "expected_sha256": sha256_of(Path(check["expected"])),
                    "expected_size": size_of(Path(check["expected"])),
                    "result": check["result"],
                    "result_before": before,
                    "result_sha256": sha256_of(result),
                    "result_size": size_of(result),
                }
            )
    for workload in plan["workloads"] if whole else []:
        launch = workload["run"]
        log = logs / f"run-{workload['name']}.log"
        ran = proc.run(launch["argv"], timeout=RUN_SECONDS, cwd="/", env=launch["env"], stderr=log)
        record["runs"].append(
            {
                "workload": workload["name"],
                "env": launch["env"],
                # Where the program's path leads, which variants.py holds to the build.
                "program": os.path.realpath(launch["argv"][0]),
                **ended(ran),
                "stdout_sha256": hashing.sha256(ran.stdout),
                "stdout_size": len(ran.stdout),
            }
        )
    schemas.write(
        out / "evidence" / "evidence.json", record, schemas.KERNELS_EVIDENCE, indent=1, sort_keys=True
    )
    return 0


if __name__ == "__main__":
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    sys.exit(main(Path(sys.argv[1])))
