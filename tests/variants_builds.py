#!/usr/bin/env python3
"""The kernel corpus's builds of libsodium, built: docs/kernels.md's "what a variant is".

It has bench/kernels/variants.py realize the baseline and bench/kernels/variants.nix's seven builds under
`tests`, at HEAD's commit, and checks what each comes to and what the variants hold:

1. The baseline and the two round trips are variants. A round trip differs from the baseline in the objects
   its table names and in no other object, by the bytes of every `.o`, with the two sets of paths the same.
2. `llc` on clang's own IR gives the baseline's code: the round trip's two Argon2 objects have the baseline's
   `.text`, `.rodata` and `.rela.text`.
3. The two wrong candidates are the named negative: the Argon2 one by libsodium's own test's answers, and the
   BLAKE2b one by that and by the output of `secretstream`, which is linked statically.
4. A skipped test, a table naming an object the build never compiles, and a table with one of a unit's two
   objects are each an error, with the check that says so.
5. A workload's launch, with the variable its command sets taken away, fails to start. And no variant's store
   path refers to another's.

It decides nothing itself about a build: it reads what the tool answered. It needs a checkout whose tracked
files are HEAD's, which the tool refuses otherwise, and a processor on which libsodium runs the units
replaced.

usage: tests/variants_builds.py
exit codes: 0 every check passed, 1 one failed, 77 the processor lacks AVX2 or AVX-512F, so nothing was built
"""

import importlib.util
import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
HERE = ROOT / "bench" / "kernels"
sys.path.append(str(ROOT / "tools"))
sys.path.append(str(HERE))
from irlean import proc, schemas  # noqa: E402


def load(name: str, path: Path) -> Any:
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


variants = load("variants", HERE / "variants.py")
# Each build, and the status and reason the tool has to give it.
BUILDS = {
    "baseline": ("variant", "built_and_checked"),
    "tests.roundtrip": ("variant", "built_and_checked"),
    "tests.blake-roundtrip": ("variant", "built_and_checked"),
    "tests.wrong-argon": ("wrong_answer", "answer_differs"),
    "tests.wrong-blake": ("wrong_answer", "answer_differs"),
    "tests.skipped": ("error", "checks_completed"),
    "tests.unused": ("error", "replaced_once"),
    "tests.half": ("error", "units_whole"),
}
ARGON = "src/libsodium/crypto_pwhash/argon2"
ARGON_OBJECTS = sorted(f"{ARGON}/{d}libavx512f_la-argon2-fill-block-avx512f.o" for d in ("", ".libs/"))
SECTIONS = (".text", ".rodata", ".rela.text")
# What failed, so far.
FAILED: list[str] = []


def check(ok: bool, what: str) -> None:
    print(f"{'ok   ' if ok else 'FAIL '} {what}")
    if not ok:
        FAILED.append(what)


def references(paths: list[str]) -> dict[str, list[str]]:
    """The store paths each of `paths` refers to, as Nix registered them."""
    ran = proc.run(["nix", "path-info", "--json", *paths], timeout=300)
    info = json.loads(ran.out) if ran.ok else {}
    found = info if isinstance(info, dict) else {i["path"]: i for i in info}
    return {path: list(found[path]["references"]) for path in paths}


def main() -> int:
    if missing := variants.missing_features():
        print(
            f"skip: this processor lacks {', '.join(missing)}, so libsodium wouldn't run the units replaced"
        )
        return 77
    said: dict[str, dict[str, Any]] = {}
    for name, (status, reason) in BUILDS.items():
        ran = proc.run([sys.executable, str(HERE / "variants.py"), "realize", name], timeout=7200, cwd=ROOT)
        answer = json.loads(ran.out) if ran.out.strip().startswith("{") else {}
        said[name] = answer
        got = (answer.get("status"), answer.get("reason"))
        exits = ran.exit == answer.get("exit_code") == variants.EXIT_CODES[status]
        check(
            got == (status, reason) and exits,
            f"{name}: {got[0]}, {got[1]}, exit {ran.exit}: {answer.get('detail')}",
        )
        check(("path" in answer) == (status == "variant"), f"{name}: a path only where it's a variant")
    if FAILED:
        return 1
    base = Path(said["baseline"]["path"])
    ours = variants.objects(base)
    check(len(ours) > 250, f"the baseline has {len(ours)} objects")
    for name in ("tests.roundtrip", "tests.blake-roundtrip"):
        theirs = variants.objects(Path(said[name]["path"]))
        differ = sorted(o for o in ours if theirs.get(o) != ours[o])
        same_paths = set(ours) == set(theirs)
        check(
            same_paths and differ == said[name]["table"],
            f"{name}: of its objects, the {len(differ)} it replaces differ",
        )
    check(
        said["tests.roundtrip"]["table"] == ARGON_OBJECTS,
        "the round trip replaces the Argon2 unit's two objects",
    )
    for obj in ARGON_OBJECTS:
        for section in SECTIONS:
            mine = variants.section(base / obj, section)
            same = mine == variants.section(Path(said["tests.roundtrip"]["path"]) / obj, section)
            check(same, f"{obj} {section}: {len(mine)} bytes, and the round trip's are the baseline's")
    argon, blake = said["tests.wrong-argon"]["checks"], said["tests.wrong-blake"]["checks"]
    check(
        not argon["answers_match"] and argon["outputs_match"],
        "wrong Argon2: the test's answers differ, and no output",
    )
    check(
        not blake["answers_match"] and not blake["outputs_match"],
        "wrong BLAKE2b: so does the static workload's output",
    )
    evidence = schemas.read(base / "evidence" / "evidence.json", schemas.KERNELS_EVIDENCE)
    for launch in evidence["runs"]:
        if launch["env"]:
            bare = proc.run(launch["argv"], timeout=1800, cwd="/", env={})
            whole = proc.run(launch["argv"], timeout=1800, cwd="/", env=launch["env"])
            check(
                whole.ok and bare.limit is None and bare.exit > 0,
                f"{launch['workload']}'s launch exits {whole.exit}, and {bare.exit} without its variable",
            )
    paths = [a["path"] for a in said.values() if "path" in a]
    for path, refers in references(paths).items():
        check(not (set(refers) & set(paths) - {path}), f"{Path(path).name} refers to no other variant")
    return 1 if FAILED else 0


if __name__ == "__main__":
    sys.exit(main())
