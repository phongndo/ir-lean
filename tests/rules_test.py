#!/usr/bin/env python3
"""Checks the rules, docs/rules.md, and the rule search, docs/rule-search.md, and that their checks can fail.

`--tier static`, in Python, with no Lean or LLVM:

- The format: a rule's statement is the Lean it should be, for flags, constants, casts, a bound instruction, a
  division at the root and below it, side conditions and a fixed width, and a malformed rule is refused for
  its reason.
- The matcher: a pattern matches what it should, and not a second occurrence that's another value, a missing
  flag, a constant that fails a side condition, or a cast the wrong way.
- Constants are computed as Lean's `BitVec` computes them.
- The IR reader: instructions the format has are read, and the rest are leaves; a cut stops at its depth; a
  term printed and read again is the same term; a slice's lines are the function's own; a rewritten function
  has the new value at each use and none of the dead cut.
- rules/Rules/Statements.lean is what rules/src generates, and the importer's record names the rules imported.
- The search's core finds the chain it should, the same way each time.

`--tier live`, with Lean, `opt`, `llc` and `llvm-mca`, one Lean process at a time:

- `import_peephole.py --check`, and `rules.py check`: every rule is proved, on the standard three axioms.
- A statement generator that prints `sub`'s operands the wrong way round stops the proof of `add_sub_cancel`.
- A rule whose statement is false has no proof: `not_proved`. Proved by `sorry`, or a true one at one width by
  `bv_decide`: `disallowed_axiom`. With a theorem of another statement: `statement_mismatch`. The others stay
  proved.
- A statement that isn't the pattern's but is still true, with a proof of its own, is refused twice over: the
  library's statements aren't what the source generates, and no application of the rule is certified.
- Certify mode on tests/rules/chain.ll: certified, as a slice, on the standard axioms, by exactly its three
  rules.
- States a broken matcher would give are refused, each for its own reason: a second occurrence that's another
  value, a side condition skipped, a flag not checked, another replacement, and another rule named. So is a
  certificate that states another claim, and one by `sorry`.
- The search on tests/rules/search.ll finds what tests/rules/expect.json says, each certified, a chain of
  three rules as a whole function and one of two as a slice, and a second run writes the same bytes.
  `llvm-mca` drops every candidate against `opt -O3`, and keeps exactly one against `llc` alone. Alive2,
  asked as a second opinion, finds each certified slice correct, and what a broken matcher would give
  incorrect.

Needs `lake build` and build/ir-lean first.
usage: tests/rules_test.py --tier static|live
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import sys
import tempfile
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
sys.path.append(str(ROOT / "tools"))
sys.path.append(str(ROOT / "tools" / "rules"))

import alive  # noqa: E402
import certify  # noqa: E402
import gen  # noqa: E402
import ir  # noqa: E402
import lang  # noqa: E402
import proved  # noqa: E402
import rules_alive  # noqa: E402
import search  # noqa: E402
from irlean import lean, proc, schemas  # noqa: E402
from irlean import verdict as core  # noqa: E402

FIXTURES = ROOT / "tests" / "rules"
RULES = [sys.executable, str(ROOT / "tools" / "rules" / "rules.py")]
IMPORT = [sys.executable, str(ROOT / "tools" / "rules" / "import_peephole.py")]
failures: list[str] = []


def report(ok: bool, what: str, detail: str = "") -> None:
    print(f"{'ok  ' if ok else 'FAIL'}  {what}")
    if not ok:
        failures.append(what)
        if detail:
            print(detail[:4000])


# ------------------------------------------------------------------------------------------------------------
# Static

STATEMENTS = {
    ("flags", "(add.nuw X -1)", "-1"): (
        "  ∀ {w : Nat} (x : Val w) (f0 : Bool),\n"
        "    Refines (Outcome.ok (Val.add x (some (BitVec.allOnes w)) true f0))"
        " (Outcome.ok (some (BitVec.allOnes w)))"
    ),
    ("same", "(add (sub Y X) X)", "Y"): (
        "  ∀ {w : Nat} (y x : Val w) (f0 f1 f2 f3 : Bool),\n"
        "    Refines (Outcome.ok (Val.add (Val.sub y x f2 f3) x f0 f1)) (Outcome.ok y)"
    ),
    ("casts", "(trunc (zext X))", "X"): (
        "  ∀ {w w1 : Nat} (x : Val w) (f0 f1 f2 : Bool),\n"
        "    w < w1 →\n"
        "    Refines (Outcome.ok (Val.trunc w (Val.zext w1 x f2) f0 f1)) (Outcome.ok x)"
    ),
    ("bound", "(or (xor A B) (bind T (or A B)))", "T"): (
        "  ∀ {w : Nat} (a b : Val w) (f0 f1 : Bool),\n"
        "    Refines (Outcome.ok (Val.or (Val.xor a b) (Val.or a b f1) f0)) (Outcome.ok (Val.or a b f1))"
    ),
    ("division_at_root", "(udiv (mul.nuw A B) B)", "A"): (
        "  ∀ {w : Nat} (a b : Val w) (f0 f1 : Bool),\n"
        "    Refines (Val.udiv (Val.mul a b true f1) b f0) (Outcome.ok a)"
    ),
    ("division_below", "(mul (udiv.exact A B) B)", "A"): (
        "  ∀ {w : Nat} (a b q0 : Val w) (f0 f1 : Bool),\n"
        "    Val.udiv a b true = Outcome.ok q0 →\n"
        "    Refines (Outcome.ok (Val.mul q0 b f0 f1)) (Outcome.ok a)"
    ),
    ("condition", "(sub.nuw C (xor A C))", "A", "(eq (c.and (c.add C 1) C) 0)"): (
        "  ∀ {w : Nat} (a : Val w) (c : BitVec w) (f0 : Bool),\n"
        "    ((c + 1#w) &&& c) = 0#w →\n"
        "    Refines (Outcome.ok (Val.sub (some c) (Val.xor a (some c)) true f0)) (Outcome.ok a)"
    ),
    ("one_bit", "(mul.nsw A:1 B)", "0"): (
        "  ∀ (a b : Val 1) (f0 : Bool),\n"
        "    Refines (Outcome.ok (Val.mul a b f0 true)) (Outcome.ok (some 0#1))"
    ),
    ("icmp", "(icmp.ult X X)", "0"): (
        "  ∀ {w : Nat} (x : Val w) (f0 : Bool),\n"
        "    Refines (Outcome.ok (Val.icmpUlt x x f0)) (Outcome.ok (some 0#1))"
    ),
    ("new_instruction", "(or.disjoint A B)", "(add.nuw.nsw A B)"): (
        "  ∀ {w : Nat} (a b : Val w),\n"
        "    Refines (Outcome.ok (Val.or a b true)) (Outcome.ok (Val.add a b true true))"
    ),
}

MALFORMED = [
    ({"name": "r", "match": "(add X Y)", "replace": "Z"}, "doesn't bind"),
    ({"name": "r", "match": "(add X", "replace": "X"}, "no `\\)`"),
    ({"name": "r", "match": "(add.exact X Y)", "replace": "X"}, "no flag"),
    ({"name": "r", "match": "(add X Y)", "replace": "(udiv X Y)"}, "can't divide"),
    ({"name": "r", "match": "(frob X Y)", "replace": "X"}, "isn't an instruction"),
    ({"name": "r", "match": "(add X)", "replace": "X"}, "takes 2 operands"),
    ({"name": "r", "match": "(add W Y)", "replace": "Y"}, "is taken"),
    ({"name": "r", "match": "(add X:8 Y:16)", "replace": "X"}, "both i8 and i16"),
    ({"name": "r", "match": "(add (bind T (or X Y)) (bind T (or X Y)))", "replace": "T"}, "bound twice"),
    ({"name": "r", "match": "X", "replace": "X"}, "has to be an instruction"),
    ({"name": "r", "match": "(trunc X)", "replace": "(zext (zext X))"}, "width the pattern doesn't fix"),
    ({"name": "Bad", "match": "(add X Y)", "replace": "X"}, "isn't a name"),
    ({"name": "r", "match": "(add X Y)", "replace": "X", "because": "x"}, "a rule has only"),
]


def leaf(name: str, width: int = 8) -> ir.Term:
    return ("leaf", f"%{name}", width)


def const(value: int, width: int = 8) -> ir.Term:
    return ("const", value & lang.mask(width), width)


def op(name: str, *args: ir.Term, flags: tuple[str, ...] = (), width: int | None = None) -> ir.Term:
    return ("op", name, flags, ir.width_of(args[-1]) if width is None else width, args)


def rule(match: str, replace: str, *where: str, name: str = "r") -> lang.Rule:
    return lang.Rule({"name": name, "match": match, "replace": replace, "where": list(where)})


def static_format() -> None:
    for key, expected in STATEMENTS.items():
        name, match, replace, *where = key
        got = rule(match, replace, *where, name=name).statement()
        report(
            got == expected,
            f"the statement of {match} to {replace} is what it should be",
            f"{got}\n-- not --\n{expected}",
        )
    for raw, why in MALFORMED:
        try:
            lang.Rule(raw)
            report(False, f"a malformed rule is refused: {raw['match']} to {raw['replace']}")
        except lang.RuleError as error:
            report(
                bool(re.search(why, str(error))),
                f"a malformed rule is refused, {why!r}: {raw['match']}",
                str(error),
            )
    report(rule("(mul (udiv.exact A B) B)", "A").divides, "a rule with a division says so")
    report(not rule("(add (sub Y X) X)", "Y").divides, "and one without doesn't")


def static_matcher() -> None:
    x, y, z = leaf("x"), leaf("y"), leaf("z")
    cancel = rule("(add (sub Y X) X)", "Y")
    report(
        cancel.apply(op("add", op("sub", y, x, flags=("nsw",)), x)) == y,
        "a pattern matches, whatever flags it leaves open",
    )
    report(
        cancel.apply(op("add", op("sub", y, x), z)) is None, "a second occurrence has to be the same value"
    )
    report(cancel.apply(op("add", x, op("sub", y, x))) is None, "operands aren't matched the other way round")
    nuw = rule("(add.nuw X -1)", "-1")
    report(
        nuw.apply(op("add", x, const(-1), flags=("nsw", "nuw"))) == const(-1), "a required flag that's there"
    )
    report(nuw.apply(op("add", x, const(-1), flags=("nsw",))) is None, "a required flag that isn't")
    report(nuw.apply(op("add", x, const(-2), flags=("nuw",))) is None, "a literal is that constant only")
    low = rule("(sub.nuw C (xor A C))", "A", "(eq (c.and (c.add C 1) C) 0)")
    report(
        low.apply(op("sub", const(7), op("xor", x, const(7)), flags=("nuw",))) == x,
        "a side condition that holds",
    )
    report(
        low.apply(op("sub", const(6), op("xor", x, const(6)), flags=("nuw",))) is None,
        "a side condition that fails",
    )
    report(
        low.apply(op("sub", const(7), op("xor", x, const(3)), flags=("nuw",))) is None,
        "one constant, used twice",
    )
    inverse = rule("(and (xor A C) (xor A (c.not C)))", "0")
    report(
        inverse.apply(op("and", op("xor", x, const(5)), op("xor", x, const(250)))) == const(0),
        "a constant expression in a pattern",
    )
    report(
        inverse.apply(op("and", op("xor", x, const(5)), op("xor", x, const(5)))) is None,
        "and one that's another value",
    )
    fold = rule("(add C0 C1)", "(c.add C0 C1)")
    report(
        fold.apply(op("add", const(200), const(100))) == const(44),
        "a constant expression in a replacement wraps",
    )
    wide = ("leaf", "%a", 16)
    back = rule("(trunc (zext X))", "X")
    report(back.apply(op("trunc", op("zext", wide, width=64), width=16)) == wide, "a cast and its inverse")
    report(back.apply(op("trunc", op("zext", wide, width=64), width=32)) is None, "a variable has one width")
    bound = rule("(or (xor A B) (bind T (or A B)))", "T")
    inner = op("or", x, y, flags=("disjoint",))
    report(
        bound.apply(op("or", op("xor", x, y), inner)) == inner,
        "a bound instruction is the replacement, flags and all",
    )
    grow = rule("(xor (and A B) -1)", "(or (xor A -1) (xor B -1))")
    want = op("or", op("xor", x, const(-1)), op("xor", y, const(-1)))
    report(grow.apply(op("xor", op("and", x, y), const(-1))) == want, "a replacement of new instructions")
    for name, value, width, expected in (
        ("pow2", 8, 8, True),
        ("pow2", 0, 8, False),
        ("pow2", 6, 8, False),
        ("msb", 128, 8, True),
        ("msb", 127, 8, False),
        ("lsb", 3, 8, True),
        ("lsb", 2, 8, False),
    ):
        r = rule("(and X C)", "X", f"({name} C)")
        got = r.apply(op("and", x, const(value, width))) is not None
        report(got == expected, f"({name} {value}) at i{width} is {expected}")
    width_rule = rule("(shl X 0)", "X", "(wgt 0)")
    report(width_rule.apply(op("shl", x, const(0))) == x, "a condition on the width")


def static_constants() -> None:
    cases = [
        ("c.not", [5], 8, 250),
        ("c.neg", [1], 8, 255),
        ("c.add", [200, 100], 8, 44),
        ("c.sub", [1, 2], 8, 255),
        ("c.urem", [7, 0], 8, 7),
        ("c.urem", [7, 3], 8, 1),
        ("c.srem", [0xF9, 3], 8, 0xFF),
        ("c.srem", [7, 0xFD], 8, 1),
        ("c.srem", [0x80, 0xFF], 8, 0),
        ("c.srem", [5, 0], 8, 5),
    ]
    for name, args, width, expected in cases:
        report(lang.cexpr_value(name, args, width) == expected, f"{name} {args} at i{width} is {expected}")
    for value, width, expected in (
        (-1, 8, 255),
        ("intmin", 8, 128),
        ("intmax", 8, 127),
        (300, 8, 44),
        (1, 1, 1),
    ):
        report(lang.literal(value, width) == expected, f"the literal {value} at i{width} is {expected}")


def static_ir() -> None:
    text = (FIXTURES / "search.ll").read_text()
    functions = {f.name: f for f in ir.functions(text)}
    report(
        sorted(functions) == ["mask", "masked", "notmask", "plain", "sum", "twice", "widths"],
        "every function is read",
    )
    total = functions["sum"]
    read = {i.name: i.op for i in total.lines if i.name}
    report(
        read
        == {
            "%i": None,
            "%acc": None,
            "%q": None,
            "%a": None,
            "%hi": "umax",
            "%lo": "umin",
            "%t": "xor",
            "%u": "xor",
            "%acc.next": "add",
            "%next": "add",
            "%done": "icmp.eq",
        },
        "instructions the format has are looked into, and a phi, a getelementptr and a load aren't",
        str(read),
    )
    report(total.defs["%next"].flags == ("nuw",), "an instruction's flags are read")
    report(ir.members(total, "%u", 2) == {"%u": 1, "%t": 2}, "a cut stops at its depth")
    cut = ir.members(total, "%u", 4)
    report(cut == {"%u": 1, "%t": 2, "%lo": 3, "%hi": 4}, "and goes through what it reads", str(cut))
    k, a = ("leaf", "%k", 32), ("leaf", "%a", 32)
    want = op("xor", op("xor", op("umin", op("umax", a, k), a), k), k)
    root = ir.term(total, "%u", 32, cut)
    report(root == want, "a cut is the term of what its root computes", str(root))
    report(ir.leaves(root) == {"%a": 32, "%k": 32}, "its leaves are the values it reads from outside")
    slice_text, declares = ir.verbatim("s0", ir.leaves(root), total, cut, "%u")
    own = {i.text for i in total.lines}
    body = slice_text.splitlines()[1:-2]
    report(
        all(line.strip() in own for line in body) and len(body) == 4,
        "a slice's lines are the function's own",
        slice_text,
    )
    report(
        declares == ["declare i32 @llvm.umax.i32(i32, i32)", "declare i32 @llvm.umin.i32(i32, i32)"],
        "with the declarations it needs",
    )
    # LLVM's own icmp-constant.ll has this: a block written before the one that runs before it.
    late = ir.functions(
        "define i1 @f(i8 %x) {\nbb1:\n  br label %bb3\n\nbb2:\n  %r = icmp eq i8 %m, 45\n  ret i1 %r\n\n"
        "bb3:\n  %m = mul nsw i8 %x, 0\n  br label %bb2\n}\n"
    )[0]
    late_cut = ir.members(late, "%r", 4)
    slice_text, _ = ir.verbatim("s0", {"%x": 8}, late, late_cut, "%r")
    report(
        slice_text.index("%m = mul") < slice_text.index("%r = icmp") and late_cut == {"%r": 1, "%m": 2},
        "a slice's lines come after what they read, whatever order the function's blocks are written in",
        slice_text,
    )
    for line, expected in (
        ("%r = add nuw nsw i8 %x, -1", ("add", ("nsw", "nuw"), 8)),
        ("%r = icmp samesign ult i16 %x, 3", ("icmp.ult", ("samesign",), 1)),
        ("%r = select i1 %c, i32 %x, i32 7", ("select", (), 32)),
        ("%r = zext nneg i8 %x to i32", ("zext", ("nneg",), 32)),
        ("%r = call i32 @llvm.ctlz.i32(i32 %x, i1 true)", ("ctlz", ("zp",), 32)),
        ("%r = call i8 @llvm.fshl.i8(i8 %x, i8 %y, i8 3)", ("fshl", (), 8)),
        ("%r = add <4 x i32> %x, %y", (None, (), 0)),
        ("%r = add i8 %x, undef", (None, (), 0)),
        ("%r = add i8 %x, poison", (None, (), 0)),
        ("%r = select <4 x i1> %c, <4 x i8> %x, <4 x i8> %y", (None, (), 0)),
        ("%r = call i32 @f(i32 %x)", (None, (), 0)),
    ):
        inst = ir.instruction(line)
        report((inst.op, inst.flags, inst.width) == expected, f"`{line}` is read as {expected[0]}")
    report(
        not ir.followed(ir.instruction("%r = udiv i8 %x, %y")),
        "a division is a leaf: the certifier doesn't follow one",
    )
    # Printing a term and reading it back gives the term.
    x, y, c = leaf("x", 16), leaf("y", 16), ("leaf", "%c", 1)
    terms = [
        op("add", op("shl", x, const(3, 16), flags=("nsw", "nuw")), y),
        op("select", c, op("or", x, y, flags=("disjoint",)), const(-1, 16)),
        op("icmp.slt", x, const(-5, 16), flags=("samesign",), width=1),
        op("zext", op("trunc", x, flags=("nuw",), width=8), flags=("nneg",), width=32),
        op("ctlz", op("umin", x, y), flags=("zp",)),
        op("abs", op("fshr", x, y, const(1, 16))),
        op("sext", op("icmp.eq", x, y, width=1), width=16),
        op("sadd_sat", op("lshr", x, y, flags=("exact",)), op("bswap", x)),
    ]
    for t in terms:
        printed, _ = ir.state("s0", {"%x": 16, "%y": 16, "%c": 1}, t)
        again = certify.function_term(ir.functions(printed)[0])
        report(again == t, f"printed and read again, the same term: {t[1]}", f"{printed}\n{again}\n{t}")
    printed, _ = ir.state("s0", {"%x": 16}, op("mul", op("or", x, const(0, 16)), op("or", x, const(0, 16))))
    report(printed.count(" or ") == 1, "one instruction, read twice, is printed once", printed)
    # A rewritten function.
    new = ir.rewritten(total, "%u", cut, a)
    report(
        "%acc.next = add i32 %acc, %a" in new
        and not re.search(r"%(hi|lo|t|u) =", new)
        and "%a = load" in new,
        "a rewritten function reads the new value, and has none of the cut that's dead",
        new,
    )
    twice = functions["twice"]
    new = ir.rewritten(twice, "%a", ir.members(twice, "%a", 4), ("leaf", "%x", 32))
    report("%r = mul i32 %x, %x" in new and "%a" not in new, "every use of the root is rewritten", new)
    masked = functions["masked"]
    new = ir.rewritten(masked, "%o", {"%o": 1, "%m": 2}, ("leaf", "%e", 32))
    report(
        "ret i32 %e" in new and "%e = add" in new and "%m" not in new,
        "what the cut reads from outside stays",
        new,
    )
    cut = ir.members(masked, "%o", 4)
    new = ir.rewritten(masked, "%o", cut, ir.term(masked, "%e", 32, cut))
    report(
        "ret i32 %e" in new and "%e = add" in new and "%m" not in new and ".rs" not in new,
        "an instruction of the cut that the new value is isn't computed again",
        new,
    )
    report(
        ir.one_block(masked) == ("%o", 32) and ir.one_block(total) is None,
        "a function of one block is known for one",
    )


def static_certificates() -> None:
    x = leaf("x")
    s, t = op("abs", op("abs", x)), op("abs", x)
    places = certify.sites(s, t)
    report(
        places == [(op("abs", x), x), (s, t)], "where a step changed, the smallest place first", str(places)
    )
    a, b = op("or", x, const(0)), x
    both = certify.sites(op("mul", a, a), op("mul", b, b))
    report(both[0] == (a, b), "one instruction read twice is one place", str(both))
    swapped = certify.sites(op("and", x, leaf("y")), op("and", leaf("y"), x))
    report(
        len(swapped) == 1 and swapped[0][0][1] == "and",
        "operands swapped is a change of the instruction",
        str(swapped),
    )
    r = rule("(or X 0)", "X", name="or_zero")
    tree = certify.proof(op("mul", a, a), op("mul", b, b), a, b, r, [100])
    lines = certify.render(tree, 4)
    report(
        lines == ["    (Rules.Mono.mul (Rules.val (Rules.or_zero _ _)) (Rules.val (Rules.or_zero _ _)))"],
        "a step's proof is a congruence around the rule",
        "\n".join(lines),
    )
    deep = x
    for i in range(40):
        deep = op("add", deep, leaf(f"y{i}"))
    target = ir.replace(deep, op("add", x, leaf("y0")), x)
    lines = certify.render(certify.proof(deep, target, op("add", x, leaf("y0")), x, r, [1000]), 4)
    report(
        max(len(line) for line in lines) <= 118 and len(lines) > 1, "a long proof is wrapped at 118 columns"
    )
    try:
        certify.proof(deep, target, op("add", x, leaf("y0")), x, r, [10])
        report(False, "a proof past its budget isn't written")
    except certify.Uncertifiable:
        report(True, "a proof past its budget isn't written")
    try:
        certify.proof(op("add", x, x), op("sub", x, x), a, b, r, [10])
        report(False, "states that differ where no rule applied have no proof")
    except certify.Uncertifiable:
        report(True, "states that differ where no rule applied have no proof")


def static_search() -> None:
    rules = search.usable(gen.load_all())
    all_rules = gen.load_all()
    report(
        len(rules) < len(all_rules) and all(not r.divides for r in rules),
        "the search leaves out rules with a division",
    )
    f = next(f for f in ir.functions((FIXTURES / "search.ll").read_text()) if f.name == "masked")
    root = ir.term(f, "%o", 32, ir.members(f, "%o", 4))
    options = search.Options()
    chain, final, states = search.best_chain(root, rules, options)
    names = [s.rule.name for s in chain]
    report(
        names == ["or_zero", "and_allOnes", "add_sub_cancel"] and final == ("leaf", "%x", 32),
        "the chain it should find",
        str(names),
    )
    again = search.best_chain(root, rules, options)
    report(again == (chain, final, states), "and the same the second time")
    short, _, _ = search.best_chain(root, rules, search.Options(steps=1))
    report(len(short) == 1, "a chain is no longer than its bound")
    _, _, reached = search.best_chain(root, rules, search.Options(states=3))
    report(reached <= 3, "and looks at no more terms than its bound")
    none, final, _ = search.best_chain(op("mul", leaf("x"), leaf("y")), rules, options)
    report(none == [] and final == op("mul", leaf("x"), leaf("y")), "nothing found is nothing reported")
    states_ = certify.states(root, chain)
    report(len(states_) == 4 and states_[-1] == ("leaf", "%x", 32), "a chain's states end at what it found")


def static_sources() -> None:
    rules = gen.load_all()
    report(
        gen.STATEMENTS.read_text() == gen.statements_text(rules),
        "rules/Rules/Statements.lean is what rules/src generates",
    )
    record = schemas.read(ROOT / "rules" / "import" / "peephole.json", schemas.RULES_IMPORT)
    names = {r.name for r in rules}
    report(
        all(e["rule"] in names for e in record["imported"])
        and record["considered"] == len(record["imported"]) + len(record["refused"]),
        "the importer's record names rules that are there, and every lemma it considered",
    )
    report(all(e["reason"] for e in record["refused"]), "each lemma it refused has its reason")
    proofs = (ROOT / "rules" / "Rules" / "Imported.lean").read_text()
    report(
        all(f"theorem {e['rule']} : Stmt.{e['rule']} := by rule_from" in proofs for e in record["imported"]),
        "and each imported rule's proof is its lemma",
    )


def static() -> None:
    static_format()
    static_matcher()
    static_constants()
    static_ir()
    static_certificates()
    static_search()
    static_sources()


# ------------------------------------------------------------------------------------------------------------
# Live


def tool(argv: list[str], timeout: float = 1500) -> proc.Ran:
    return proc.run(argv, cwd=ROOT, timeout=timeout)


def overlay(work: Path, statements: str, modules: dict[str, str]) -> dict[str, proc.Ran]:
    """Another build of the `Rules` library in `work`: Rules/Mono.lean as it is, `statements`, and each of
    `modules`, a name and its text, then a root importing them all. Returns how each compile ended."""
    source = ROOT / "rules" / "Rules"
    (work / "Rules").mkdir(parents=True)
    texts = {"Mono": (source / "Mono.lean").read_text(), "Statements": statements, **modules}
    root = "".join(f"import Rules.{name}\n" for name in texts)
    env = lean.env(work, pin=True)
    ran = {}
    for name, text in texts.items():
        (work / "Rules" / f"{name}.lean").write_text(text)
        ran[name] = proc.run(
            lean.argv(4096, "-o", f"Rules/{name}.olean", f"Rules/{name}.lean"), cwd=work, env=env, timeout=600
        )
    (work / "Rules.lean").write_text(root)
    ran["Rules"] = proc.run(
        lean.argv(4096, "-o", "Rules.olean", "Rules.lean"), cwd=work, env=env, timeout=600
    )
    return ran


def caught(ran: proc.Ran, pattern: str) -> core.Decision:
    """Whether Lean failed on its own, with an error matching `pattern`, which isn't a limit."""
    errors = [m.text for m in lean.messages(ran.output) if m.severity == "error"]
    own = [e for e in errors if re.search(pattern, e) and not lean.is_limit(e)]
    return core.decide(
        core.Verdict.CAUGHT, core.Evidence(step=core.Step.of("lean", ran), finding=own[0] if own else None)
    )


IMPORTED = (ROOT / "rules" / "Rules" / "Imported.lean").read_text()
WRONG = {"name": "add_one_wrong", "match": "(add X 1)", "replace": "X"}
ONE_WIDTH = {"name": "xor_and_xor_i8", "match": "(xor (and X:8 Y) (xor X Y))", "replace": "(or X Y)"}
EXTRA_HEADER = (
    "import Rules.Mono\nimport Rules.Statements\nimport IRLean.Generic.Arith\n\n"
    "open IRLean\n\nnamespace Rules\n\n"
)


def live_rules() -> None:
    ran = tool([*RULES, "gen", "--check"])
    report(ran.exit == 0, "rules.py gen --check: the statements are what the source generates", ran.output)
    ran = tool([*IMPORT, "--check"])
    report(
        ran.exit == 0,
        "import_peephole.py --check: the imported rules are what the importer writes",
        ran.output,
    )
    record = proved.check()
    bad = [e for e in record["rules"] if not e["proved"]]
    report(
        not bad and len(record["rules"]) >= 180,
        f"every one of {len(record['rules'])} rules is proved",
        json.dumps(bad[:3]),
    )
    standard = {"propext", "Classical.choice", "Quot.sound"}
    report(
        all(set(e.get("axioms", ["?"])) <= standard for e in record["rules"]),
        "each on the standard three axioms",
    )

    rules = gen.load_all()
    with tempfile.TemporaryDirectory(dir=ROOT / "build") as temporary:
        base = Path(temporary)

        # A statement generator that prints `sub`'s operands the wrong way round.
        right = lang.Rule.statement
        try:
            lang.Rule.statement = lambda self: re.sub(
                r"Val\.sub (\w+) (\w+) ", r"Val.sub \2 \1 ", right(self)
            )  # type: ignore[method-assign]
            broken = gen.statements_text(rules)
        finally:
            lang.Rule.statement = right  # type: ignore[method-assign]
        ran = overlay(base / "generator", broken, {"Imported": IMPORTED})
        lines = IMPORTED.splitlines()
        failed = {
            lines[m.line - 1].split()[1]
            for m in lean.messages(ran["Imported"].output)
            if m.severity == "error" and m.line <= len(lines) and lines[m.line - 1].startswith("theorem ")
        }
        decision = caught(ran["Imported"], "could not unify|mismatch|failed")
        report(
            decision.granted and "add_sub_cancel" in failed and "or_zero" not in failed,
            "a statement generator that swaps `sub`'s operands stops the proof of add_sub_cancel, with an "
            "error of its own",
            f"{decision}\n{sorted(failed)}\n{ran['Imported'].output[:1500]}",
        )

        # A rule whose statement is false, and what a proof of it would have to be.
        more = [*rules, lang.Rule(WRONG), lang.Rule(ONE_WIDTH)]
        statements = gen.statements_text(more)
        attempt = (
            EXTRA_HEADER
            + "theorem add_one_wrong : Stmt.add_one_wrong := by rule_from IRLean.Generic.add_zero\n"
            + "\nend Rules\n"
        )
        ran = overlay(base / "false", statements, {"Imported": IMPORTED, "Extra": attempt})
        decision = caught(ran["Extra"], "could not unify|mismatch|failed")
        report(
            decision.granted,
            "a false rule's proof from a lemma about another rewrite fails",
            f"{decision}\n{ran['Extra'].output[:1500]}",
        )

        def refused(directory: str, extra: str, name: str, reason: str, what: str) -> None:
            ran = overlay(
                base / directory,
                statements,
                {"Imported": IMPORTED, "Extra": EXTRA_HEADER + extra + "\nend Rules\n"},
            )
            if ran["Rules"].exit != 0:
                report(False, what, "\n".join(r.output[:800] for r in ran.values()))
                return
            got = {e["name"]: e for e in proved.check(more, base / directory)["rules"]}
            others = [e for e in got.values() if e["name"] not in (WRONG["name"], ONE_WIDTH["name"])]
            report(
                not got[name]["proved"]
                and got[name]["reason"] == reason
                and all(e["proved"] for e in others),
                what,
                json.dumps(got[name]),
            )

        refused("none", "", "add_one_wrong", "not_proved", "a rule with no theorem isn't proved: not_proved")
        refused(
            "sorry",
            "theorem add_one_wrong : Stmt.add_one_wrong := sorry\n",
            "add_one_wrong",
            "disallowed_axiom",
            "a false rule proved by `sorry` isn't proved: disallowed_axiom",
        )
        refused(
            "other",
            "theorem add_one_wrong : ∀ {w : Nat} (x : Val w), Refines (Outcome.ok x) (Outcome.ok x) :=\n"
            "  fun x => Rules.ok (Refines.refl x)\n",
            "add_one_wrong",
            "statement_mismatch",
            "a theorem of another statement proves no rule: statement_mismatch",
        )
        refused(
            "bv_decide",
            "theorem xor_and_xor_i8 : Stmt.xor_and_xor_i8 := by\n  intro x y\n  refine Rules.ok ?_\n"
            "  cases x with\n"
            "  | none => exact Refine.val_none _\n  | some v =>\n    cases y with\n"
            "    | none => exact Refine.val_none _\n    | some u =>\n"
            "      have h : (v &&& u) ^^^ (v ^^^ u) = v ||| u := by bv_decide\n"
            "      simp [Val.and, Val.xor, Val.or, Val.map₂, Refines, Refine.le, h]\n",
            "xor_and_xor_i8",
            "disallowed_axiom",
            "a true rule proved at one width by `bv_decide` isn't proved: disallowed_axiom",
        )

        # A statement that isn't the pattern's, but true, with a proof of its own.
        swapped = gen.statements_text(rules).replace(
            "Refines (Outcome.ok (Val.xor a (some 0#w))) (Outcome.ok a)",
            "Refines (Outcome.ok (Val.xor (some 0#w) a)) (Outcome.ok a)",
        )
        own = IMPORTED.replace(
            "theorem xor_zero : Stmt.xor_zero := by rule_from_eq IRLean.Generic.xor_zero",
            "theorem xor_zero : Stmt.xor_zero := by\n  intro w a\n  refine Rules.ok ?_\n"
            "  rw [Peephole.Lemmas.Logic.xor_comm, IRLean.Generic.xor_zero]\n  exact IRLean.Refines.refl _",
        )
        ran = overlay(base / "true", swapped, {"Imported": own})
        report(
            swapped != gen.statements_text(rules) and own != IMPORTED and ran["Rules"].exit == 0,
            "a statement of xor_zero with its operands swapped is still true, and has a proof",
            "\n".join(r.output[:800] for r in ran.values()),
        )
        got = proved.check(rules, base / "true")["rules"]
        report(
            not any(e["proved"] for e in got) and got[0]["reason"] == "check_failed",
            "but a library whose statements aren't what the source generates proves no rule",
            json.dumps(got[0]),
        )
        module = STATES.format(
            width=8, params="i8 %x", before="  %r = xor i8 %x, 0\n  ret i8 %r", after="  ret i8 %x"
        )
        by_name = {r.name: r for r in rules}
        verdict = certify.check(
            module, [by_name["xor_zero"]], base / "true-cert", "slice", overlay=base / "true"
        )
        report(
            verdict["status"] == "refused" and verdict["reason"] == "proof_failed",
            "and no application of the rule as the pattern has it is certified against it",
            json.dumps(verdict)[:1500],
        )
        verdict = certify.check(module, [by_name["xor_zero"]], base / "true-ok", "slice")
        report(
            verdict["status"] == "certified", "which the real library certifies", json.dumps(verdict)[:1500]
        )


STATES = """target triple = "x86_64-unknown-linux-gnu"

define i{width} @s0({params}) {{
{before}
}}

define i{width} @s1({params}) {{
{after}
}}
"""

# What a broken matcher would give, the rule it would name, and why Lean refuses it.
BROKEN = [
    (
        "a second occurrence that's another value",
        "add_sub_cancel",
        {
            "width": 8,
            "params": "i8 %x, i8 %y, i8 %z",
            "before": "  %d = sub i8 %x, %y\n  %e = add i8 %d, %z\n  ret i8 %e",
            "after": "  ret i8 %x",
        },
        r"[Mm]ismatch",
    ),
    (
        "a side condition skipped",
        "sub_mask_xor_nuw",
        {
            "width": 8,
            "params": "i8 %a",
            "before": "  %x = xor i8 %a, 6\n  %s = sub nuw i8 6, %x\n  ret i8 %s",
            "after": "  ret i8 %a",
        },
        r"decide",
    ),
    (
        "a flag not checked",
        "add_nuw_allOnes",
        {
            "width": 8,
            "params": "i8 %x",
            "before": "  %r = add i8 %x, -1\n  ret i8 %r",
            "after": "  ret i8 -1",
        },
        r"[Mm]ismatch",
    ),
    (
        "another replacement",
        "or_zero",
        {"width": 8, "params": "i8 %x", "before": "  %r = or i8 %x, 0\n  ret i8 %r", "after": "  ret i8 0"},
        r"[Mm]ismatch",
    ),
    (
        "another rule named",
        "or_zero",
        {
            "width": 8,
            "params": "i8 %x",
            "before": "  %r = and i8 %x, -1\n  ret i8 %r",
            "after": "  ret i8 %x",
        },
        r"[Mm]ismatch",
    ),
]


def live_certify(work: Path) -> None:
    by_name = {r.name: r for r in gen.load_all()}
    ran = tool(
        [
            *RULES,
            "certify",
            str(FIXTURES / "chain.ll"),
            "--rule",
            "or_zero",
            "--rule",
            "and_allOnes",
            "--rule",
            "add_sub_cancel",
            "--out",
            str(work / "chain"),
        ]
    )
    verdict: dict[str, Any]
    try:
        verdict = schemas.loads(ran.out, schemas.RULES_CERTIFICATE)
    except schemas.SchemaError as error:
        verdict = {"status": str(error), "claim": {}, "tier": {}, "rules_used": [], "axioms": ["?"]}
    report(
        ran.exit == 0
        and verdict["status"] == "certified"
        and verdict["claim"]["statement"] == "IRLean.Refines Chain.s0 Chain.s3"
        and verdict["tier"] == {"scope": "slice", "axioms": "standard"}
        and verdict["rules_used"] == ["add_sub_cancel", "and_allOnes", "or_zero"]
        and set(verdict["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"},
        "certify mode on tests/rules/chain.ll: three rules, certified as a slice on the standard axioms",
        ran.output[:3000],
    )
    cert = (work / "chain" / "ChainCert.lean").read_text()
    report(
        "IRLean.Refines.trans (IRLean.Refines.trans Cert.step_0 Cert.step_1) Cert.step_2" in cert
        and "bv_decide" not in cert
        and "sorry" not in cert,
        "its certificate is the three steps composed by transitivity, with no `bv_decide`",
    )
    ran = tool(
        [
            *RULES,
            "certify",
            str(FIXTURES / "chain.ll"),
            "--rule",
            "or_zero",
            "--rule",
            "add_sub_cancel",
            "--rule",
            "and_allOnes",
            "--out",
            str(work / "order"),
        ]
    )
    report(
        ran.exit == 1 and '"status": "refused"' in ran.out,
        "the same states with two rules named out of order: refused",
        ran.output[:1500],
    )
    for i, (what, name, parts, why) in enumerate(BROKEN):
        verdict = certify.check(STATES.format(**parts), [by_name[name]], work / f"broken{i}", "slice")
        report(
            verdict["status"] == "refused"
            and verdict["reason"] == "proof_failed"
            and bool(re.search(why, verdict["detail"]))
            and not lean.is_limit(verdict["detail"]),
            f"states a broken matcher would give are refused, {what}: proof_failed, {why!r}",
            json.dumps(verdict)[:1500],
        )
    # The same from matchers generated from a wrong pattern, run by the search's own core.
    loose = [
        (
            "add_sub_cancel",
            {"match": "(add (sub B A) Z)", "replace": "B"},
            op("add", op("sub", leaf("x"), leaf("y")), leaf("z")),
        ),
        (
            "sub_mask_xor_nuw",
            {"match": "(sub.nuw C (xor A C))", "replace": "A"},
            op("sub", const(6), op("xor", leaf("a"), const(6)), flags=("nuw",)),
        ),
    ]
    for i, (name, wrong, root) in enumerate(loose):
        mutant = lang.Rule({"name": name, **wrong})
        chain, _, _ = search.best_chain(root, [mutant], search.Options())
        fired = bool(chain) and by_name[name].apply(root) is None
        params = ir.leaves(root)
        texts = (
            [ir.state(f"s{k}", params, t) for k, t in enumerate(certify.states(root, chain))] if chain else []
        )
        verdict = (
            certify.check(certify.chain_module("", texts), [by_name[name]], work / f"loose{i}", "slice")
            if chain
            else {}
        )
        report(
            fired and verdict.get("status") == "refused" and verdict.get("reason") == "proof_failed",
            f"a matcher generated from a wrong pattern of {name} fires where the rule doesn't, and isn't "
            "certified",
            json.dumps(verdict)[:1500],
        )
    good = STATES.format(
        width=8, params="i8 %x", before="  %r = or i8 %x, 0\n  ret i8 %r", after="  ret i8 %x"
    )
    header = "import Rules\nimport Chain\n\nopen IRLean\n\n"
    verdict = certify.check(
        good, [by_name["or_zero"]], work / "claim", "slice", header + "theorem Cert.cert : True := trivial\n"
    )
    report(
        verdict["status"] == "refused" and verdict["reason"] == "claim_type_mismatch",
        "a certificate that states another claim: claim_type_mismatch",
        json.dumps(verdict)[:1500],
    )
    verdict = certify.check(
        good,
        [by_name["or_zero"]],
        work / "sorry",
        "slice",
        header + "theorem Cert.cert : IRLean.Refines Chain.s0 Chain.s1 := sorry\n",
    )
    report(
        verdict["status"] == "refused"
        and "sorryAx" in verdict["axioms"]
        and verdict["tier"]["axioms"] is None,
        "a certificate by `sorry`: refused, its axioms aren't allowed",
        json.dumps(verdict)[:1500],
    )
    verdict = certify.check(good, [by_name["or_zero"]], work / "good", "slice")
    report(
        verdict["status"] == "certified",
        "and the right certificate for the same states is certified",
        json.dumps(verdict)[:1500],
    )
    bad_ir = good.replace("ret i8 %x\n}\n", "ret i8 %nothing\n}\n", 1) if good.count("ret i8 %x") else good
    verdict = certify.check(
        bad_ir.replace("  ret i8 %x", "  ret i8 %q"), [by_name["or_zero"]], work / "ir", "slice"
    )
    report(
        verdict["status"] == "error" and verdict["reason"] == "ir_invalid",
        "states that aren't valid IR: ir_invalid",
        json.dumps(verdict)[:800],
    )
    memory = STATES.format(
        width=8,
        params="ptr %p",
        before="  %a = load i8, ptr %p\n  %r = or i8 %a, 0\n  ret i8 %r",
        after="  %a = load i8, ptr %p\n  ret i8 %a",
    )
    verdict = certify.check(memory, [by_name["or_zero"]], work / "memory", "slice")
    report(
        verdict["status"] == "unsupported",
        "states that read memory: unsupported, never certified",
        json.dumps(verdict)[:800],
    )


def summarize(record: dict[str, Any]) -> list[Any]:
    """What a search found, as tests/rules/expect.json has it."""
    out = []
    for f in record["functions"]:
        for r in f["results"]:
            out.append(
                {
                    "function": f["function"],
                    "root": r["root"],
                    "rules": [s["rule"] for s in r["chain"]],
                    "at": [s["at"] for s in r["chain"]],
                    "instructions": [r["instructions"]["before"], r["instructions"]["after"]],
                    "kept": r["kept"],
                    "slice": r.get("slice", {}).get("status"),
                    "function_status": r.get("function", {}).get("status"),
                }
            )
    return out


def live_search(work: Path) -> None:
    fixture = str(FIXTURES / "search.ll")
    first = tool([*RULES, "search", fixture, "--keep", "all", "--out", str(work / "a")])
    report(
        first.exit == 0,
        "rules.py search on tests/rules/search.ll, keeping every candidate",
        first.output[-3000:],
    )
    if first.exit != 0:
        return
    record = schemas.read(work / "a" / "results.json", schemas.RULE_SEARCH)
    expected = json.loads((FIXTURES / "expect.json").read_text())
    got = summarize(record)
    report(
        got == expected["results"], "it finds what tests/rules/expect.json says", json.dumps(got, indent=1)
    )
    results = [r for f in record["functions"] for r in f["results"]]
    report(all(r["slice"]["status"] == "certified" for r in results), "each as a certified slice")
    long = [r for r in results if len(r["chain"]) >= 2 and r["slice"]["status"] == "certified"]
    whole = [
        r
        for r in long
        if r["function"]["status"] == "certified" and r["function"]["tier"]["scope"] == "function"
    ]
    report(
        len(long) >= 2 and len(whole) >= 1,
        "a chain of two or more rules, as a slice, and one as a whole function too",
    )
    report(
        all(r["slice"]["tier"] == {"scope": "slice", "axioms": "standard"} for r in results),
        "every certificate rests on the standard three axioms",
    )
    total = next(r for f in record["functions"] if f["function"] == "sum" for r in f["results"])
    report(
        total["function"]["status"] == "not attempted" and total["slice"]["tier"]["scope"] == "slice",
        "a function with a loop and a load is certified as a slice only",
    )
    after = (work / "a" / total["directory"] / "after.ll").read_text()
    report(
        "%acc.next = add i32 %acc, %a" in after
        and "@llvm.umax" not in after.split("define i32 @sum")[1].split("\n}")[0],
        "its rewritten function reads the load directly",
        after,
    )
    cert = (work / "a" / total["directory"] / "slice" / "ChainCert.lean").read_text()
    report(
        "Rules.xor_xor_cancel" in cert and "Rules.umin_umax_left" in cert and "IRLean.Refines.trans" in cert,
        "and its certificate composes the two rules",
    )
    if shutil.which("alive-tv") is None:
        report(False, "alive-tv is on PATH, to ask Alive2 about what was certified")
    else:
        said = rules_alive.check([work / "a"])
        report(
            not said["incorrect"] and len(said["correct"]) == len(results),
            f"Alive2 finds each of the {len(results)} certified slices correct too",
            json.dumps(said),
        )
        with tempfile.TemporaryDirectory() as scratch:
            before, after = STATES.format(**BROKEN[0][2]).split("define i8 @s1")
            wrong = alive.verdict(
                alive.run(before, before.split("define")[0] + "define i8 @s0" + after, scratch)
            )
        report(
            wrong == "incorrect", "and what a broken matcher would give incorrect, as Lean refuses it", wrong
        )
    second = tool([*RULES, "search", fixture, "--keep", "all", "--out", str(work / "b")])
    same = (
        second.exit == 0
        and (work / "a" / "results.json").read_bytes() == (work / "b" / "results.json").read_bytes()
    )
    files = sorted(p.relative_to(work / "a") for p in (work / "a").rglob("*") if p.suffix in (".ll", ".lean"))
    same = same and all((work / "a" / p).read_bytes() == (work / "b" / p).read_bytes() for p in files)
    report(
        same and len(files) > 20,
        f"a second run writes the same bytes: results.json and {len(files)} IR and Lean files",
    )
    report(first.out == second.out.replace(str(work / "b"), str(work / "a")), "and prints the same")
    default = tool([*RULES, "search", fixture, "--out", str(work / "c")])
    record = schemas.read(work / "c" / "results.json", schemas.RULE_SEARCH)
    results = [r for f in record["functions"] for r in f["results"]]
    report(
        default.exit == 0
        and bool(results)
        and not any(r["kept"] for r in results)
        and all(r["llvm_mca"]["verdict"] == "same" for r in results),
        "against `opt -O3`, llvm-mca finds no candidate cheaper, and none is kept",
        default.output[-2000:],
    )
    alone = tool([*RULES, "search", fixture, "--baseline", "none", "--out", str(work / "d")])
    record = schemas.read(work / "d" / "results.json", schemas.RULE_SEARCH)
    kept = [(f["function"], r["root"]) for f in record["functions"] for r in f["results"] if r["kept"]]
    one = next((r for f in record["functions"] for r in f["results"] if r["kept"]), {})
    report(
        alone.exit == 0
        and kept == [("sum", "%u")]
        and one["llvm_mca"]["uops_after"] < one["llvm_mca"]["uops_before"]
        and one["slice"]["status"] == "certified",
        "against `llc` alone, it keeps the one candidate with fewer uOps, certified",
        alone.output[-2000:],
    )
    bigger = search.uops(
        STATES.format(
            width=32,
            params="i32 %x, i32 %y",
            before="  %a = mul i32 %x, %y\n  %b = udiv i32 %a, %y\n  ret i32 %b",
            after="  ret i32 %x",
        ).split("define i32 @s1")[0],
        search.Options(baseline="none"),
    )
    smaller = search.uops(
        'target triple = "x86_64-unknown-linux-gnu"\ndefine i32 @s0(i32 %x, i32 %y) {\n  ret i32 %x\n}\n',
        search.Options(baseline="none"),
    )
    report(
        bigger is not None and smaller is not None and smaller < bigger,
        "llvm-mca counts more uOps for more code",
        f"{bigger} {smaller}",
    )
    missing = tool([*RULES, "search", fixture, "--function", "nothing", "--out", str(work / "e")])
    report(missing.exit == 1 and "no function" in missing.out, "a function that isn't there is an error")


def live() -> None:
    if not (ROOT / "build" / "ir-lean").exists():
        report(False, "build/ir-lean is there: run cmake and ninja first")
        return
    for name in ("opt", "llc", "llvm-mca", "lean", "leanchecker"):
        if shutil.which(name) is None:
            report(False, f"{name} is on PATH: run inside nix develop")
            return
    live_rules()
    with tempfile.TemporaryDirectory(dir=ROOT / "build") as temporary:
        live_certify(Path(temporary) / "certify")
        live_search(Path(temporary) / "search")


def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("--tier", choices=("static", "live"), required=True)
    args = parser.parse_args()
    (ROOT / "build").mkdir(exist_ok=True)
    (static if args.tier == "static" else live)()
    if failures:
        print(f"\n{len(failures)} failed:\n" + "\n".join(f"  {f}" for f in failures))
        return 1
    print("\nall passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
