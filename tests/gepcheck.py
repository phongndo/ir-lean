#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Checks `getelementptr`'s flags, through the emitter, against Alive2.

Comparing with native code can't see these rules, since a poison pointer usually runs fine. So each case
runs in the model on several layouts, and then:
  - If the answer doesn't depend on the layout, Alive2 must prove that answer and the instruction refine
    each other.
  - If it does, then Alive2 must find a layout where the instruction is poison and the answer isn't.

usage: tests/gepcheck.py path/to/ir-lean
"""

import itertools
import os
import shutil
import sys
import tempfile

import alive
from opcheck import NATIVE, lean_env, sh

FLAGS = ["", "inbounds", "nusw", "nuw", "inbounds nuw", "nusw nuw"]
GLOBAL = "@g = constant [8 x i8] zeroinitializer, align 1\n"
HUGE = [(1 << 63) - 1, -(1 << 63), 1 << 61, -(1 << 61)]
# Addresses for @g in the model, which has to be a valid address for all 8 bytes and the one after. An
# answer can only change where the offsets so far carry an address past 0 or the top, so these sit around
# those points, for any two of the large offsets the cases use and for the small ones.
LAYOUTS = sorted(
    {
        a % (1 << 64)
        for x, y in itertools.product([0, *HUGE], repeat=2)
        for a in range(x + y - 40, x + y + 41)
        if 1 <= a % (1 << 64) <= (1 << 64) - 9
    }
)


def cases():
    """Yields each case's body, which leaves the result in %p, or a pair of the body for the emitter and the
    same thing for Alive2."""
    bases = [0, 4, 8, 9, -1]
    for f, b, d in itertools.product(FLAGS, bases, [-9, -8, -4, -1, 0, 1, 4, 8, 9, *HUGE]):
        yield (
            f"%base = getelementptr i8, ptr @g, i64 {b}\n"  #
            f"  %p = getelementptr {f} i8, ptr %base, i64 {d}"
        )
    # Each index is a step, so these go out and back, or stop at the end on the way.
    for f, b, i, j in itertools.product(FLAGS, [0, 4, 9], [-1, 0, 1, 2, 3], [-8, -4, -1, 0, 1, 4]):
        yield (
            f"%base = getelementptr i8, ptr @g, i64 {b}\n"
            f"  %p = getelementptr {f} [4 x i8], ptr %base, i64 {i}, i64 {j}"
        )
    # Partial sums, multiplication, and a struct's field.
    for f, i, j in itertools.product(FLAGS, HUGE, HUGE):
        yield f"%p = getelementptr {f} [1 x i8], ptr @g, i64 {i}, i64 {j}"
    for f, i in itertools.product(FLAGS, [0, 1, 2, 3, -1, 1 << 61, 1 << 62, -(1 << 61)]):
        yield f"%i = add i64 0, {i}\n  %p = getelementptr {f} i64, ptr @g, i64 %i"
        # Alive2 doesn't apply the multiplication rules to a literal index, though it does to this same value
        # in `%i`, and LangRef doesn't tell them apart. So the emitter gets the literal, and Alive2 `%i`.
        yield (
            f"%p = getelementptr {f} i64, ptr @g, i64 {i}",
            f"%i = add i64 0, {i}\n  %p = getelementptr {f} i64, ptr @g, i64 %i",
        )
        yield f"%p = getelementptr {f} {{ i32, [4 x i8] }}, ptr @g, i64 0, i32 1, i64 {i}"
    # The only pointer in bounds of null is null.
    for f, d in itertools.product(FLAGS, [-1, 0, 1, 8]):
        yield f"%p = getelementptr {f} i8, ptr null, i64 {d}"


def model(tool, bodies, work):
    """Each case's answer on each layout: `poison`, or `block:offset`."""
    source = GLOBAL + "".join(
        f"define ptr @c{n}() {{\n  {b}\n  ret ptr %p\n}}\n" for n, b in enumerate(bodies)
    )
    ll, lean = os.path.join(work, "cases.ll"), os.path.join(work, "Cases.lean")
    with open(ll, "w") as f:
        f.write(source)
    sh([tool, ll, "-o", lean, "--namespace", "Cases"])
    env = lean_env(work)
    sh(["lean", "-R", work, "-o", os.path.join(work, "Cases.olean"), lean], env=env)
    src = [
        "import Cases",
        "open IRLean",
        "set_option maxRecDepth 1000000",
        "def show' : Outcome (PtrVal × Mem) → String",
        '  | some (.ok (some p, _)) => s!"{p.block}:{p.offset.toNat}"',
        '  | some (.ok (none, _)) => "poison"',
        '  | _ => "stopped"',
    ]
    runners = []
    for n in range(len(bodies)):
        src.append(f"def r{n} (b : Nat → BitVec 64) : String := show' (Cases.c{n} (Cases.initial b))")
        runners.append(f"r{n}")
    src.append(f"def main : IO Unit := for l in ({LAYOUTS} : List Nat) do")
    src.append(f"  for r in [{', '.join(runners)}] do IO.println (r fun _ => BitVec.ofNat 64 l)")
    path = os.path.join(work, "Drive.lean")
    with open(path, "w") as f:
        f.write("\n".join(src) + "\n")
    out = sh(["lean", *NATIVE, "--run", path], env=env).stdout.split()
    if len(out) != len(LAYOUTS) * len(bodies):
        sys.exit("Lean printed the wrong number of results")
    return [out[n :: len(bodies)] for n in range(len(bodies))]


def as_ir(answer):
    if answer == "poison":
        return "%r = getelementptr i8, ptr poison, i64 0\n  ret ptr %r"
    block, offset = (int(x) for x in answer.split(":"))
    signed = offset - (1 << 64) if offset >= 1 << 63 else offset
    base = {0: "null", 1: "@g"}[block]
    return f"%r = getelementptr i8, ptr {base}, i64 {signed}\n  ret ptr %r"


def verdict(output):
    """Alive2's verdict on one pair: True, False, or None if it can't tell."""
    if output is None or ("1 correct transformations" in output and "0 incorrect" in output):
        return True
    if "1 incorrect transformations" in output:
        return False
    return None


def function(body):
    return f"define ptr @F() {{\n  {body}\n}}\n"


def classify(job, forward, back):
    """Returns (case, kind, what's wrong or empty)."""
    body, answers, _ = job
    if len(set(answers)) == 1:
        if forward is None or back is None:
            return body, "unchecked", f"answer {answers[0]}: alive2 couldn't tell"
        if forward and back:
            return body, "exact", ""
        return (
            body,
            "wrong",
            f"answer {answers[0]}: instruction refines it {forward}, it refines instruction {back}",
        )
    if forward is None or back is None:
        return body, "unchecked", f"answers {answers}: alive2 couldn't tell"
    if forward and not back:
        return body, "layout", ""
    return (
        body,
        "wrong",
        f"answers {answers}: instruction refines it {forward}, it refines instruction {back}",
    )


def check_all(jobs, work):
    """Returns (case, kind, what's wrong or empty) for each job, in order."""
    results = [None] * len(jobs)
    pairs, asked = [], []
    for n, (body, answers, _) in enumerate(jobs):
        if "stopped" in answers:
            results[n] = (body, "wrong", f"the model stopped: {answers}")
            continue
        values = [a for a in answers if a != "poison"]
        if len(set(answers)) != 1 and (len(values) == len(answers) or not values):
            results[n] = (
                body,
                "wrong",
                f"the answer changes with the layout in a way flags can't explain: {answers}",
            )
            continue
        instruction = function(f"{body}\n  ret ptr %p")
        table = function(as_ir(answers[0] if len(set(answers)) == 1 else values[0]))
        pairs += [(instruction, table), (table, instruction)]
        asked.append(n)
    verdicts = [verdict(o) for o in alive.refinements(GLOBAL, pairs, work)]
    for k, n in enumerate(asked):
        results[n] = classify(jobs[n], verdicts[2 * k], verdicts[2 * k + 1])
    return results


def main():
    tool = os.path.abspath(sys.argv[1])
    if not shutil.which("alive-tv"):
        sys.exit("FAIL  alive2: alive-tv is not on PATH")
    work = tempfile.mkdtemp(prefix="gepcheck-")
    try:
        pairs = [c if isinstance(c, tuple) else (c, c) for c in cases()]
        answers = model(tool, [p[0] for p in pairs], work)
        jobs = [(p[1], a, work) for p, a in zip(pairs, answers, strict=True)]
        results = check_all(jobs, work)
        count = {k: sum(r[1] == k for r in results) for k in ("exact", "layout", "unchecked", "wrong")}
        print(
            f"{len(results)} cases: {count['exact']} proved exact, {count['layout']} depend on the layout as "
            f"Alive2 agrees, {count['unchecked']} it couldn't check, {count['wrong']} wrong"
        )
        for body, kind, why in results:
            if kind in ("wrong", "unchecked"):
                print(f"  {kind.upper()} {' / '.join(body.split(chr(10)))}\n    {why}")
        sys.exit(1 if count["wrong"] or count["unchecked"] else 0)
    finally:
        shutil.rmtree(work, ignore_errors=True)


if __name__ == "__main__":
    main()
