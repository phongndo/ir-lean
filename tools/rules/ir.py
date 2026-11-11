"""LLVM IR as text, as far as the rules need it: scalar integer instructions as terms, cuts, and printing a
term back as instructions.

A function is read from what `opt -S` prints. Only instructions the format has are looked into: the integer
binary operators, `icmp`, `select` on an `i1`, the integer casts and the integer intrinsics, with operands
that are values or integer literals. Everything else, a `phi`, a `load`, a call, a vector, is a line of text
that defines a value, and a leaf wherever it's used. Nothing here is trusted: a slice or a rewritten function
is checked by `opt -passes=verify`, and a certificate is about what `build/ir-lean` then translates.

A division can be undefined, so the certifier doesn't follow one yet: it's a leaf too.
"""

from __future__ import annotations

import re
from collections.abc import Iterable
from dataclasses import dataclass, field

import lang

Term = lang.Term

NAME = r'%(?:[-a-zA-Z$._0-9]+|"[^"\n]*")'
VALUE = rf"(?:{NAME}|-?\d+|true|false)"
FLAG = r"(?: (?:nuw|nsw|exact|disjoint|nneg))*"

BINARY = re.compile(
    rf"(add|sub|mul|shl|lshr|ashr|udiv|sdiv|urem|srem|and|or|xor)({FLAG}) i(\d+) ({VALUE}), ({VALUE})"
)
ICMP = re.compile(rf"icmp( samesign)? (eq|ne|ugt|uge|ult|ule|sgt|sge|slt|sle) i(\d+) ({VALUE}), ({VALUE})")
SELECT = re.compile(rf"select i1 ({VALUE}), i(\d+) ({VALUE}), i(\d+) ({VALUE})")
CAST = re.compile(rf"(zext|sext|trunc)({FLAG}) i(\d+) ({VALUE}) to i(\d+)")
CALL = re.compile(rf"(?:tail )?call i(\d+) @llvm\.([a-z.]+)\.i(\d+)\(((?:i\d+ {VALUE}(?:, )?)+)\)")
ARGUMENT = re.compile(rf"i(\d+) ({VALUE})")
DEFINE = re.compile(r"define\b.*?@([-a-zA-Z$._0-9]+|\"[^\"]*\")\(")
ASSIGN = re.compile(rf"({NAME}) = (.*)")
RET = re.compile(rf"ret i(\d+) ({VALUE})")
LABEL = re.compile(r"([-a-zA-Z$._0-9]+|\"[^\"]*\"):")

INTRINSICS = {info.llvm: op for op, info in lang.OPS.items() if info.kind == "intr"}
# The intrinsics whose last operand is an `i1` constant, which the format reads as a flag.
BOOL_FLAG = {"ctlz": "zp", "cttz": "zp", "abs": "imp"}


class IRError(ValueError):
    """IR this can't read or write."""


@dataclass
class Inst:
    """One line of a block. `op` and the rest are set only for an instruction the format has."""

    text: str
    name: str | None = None
    op: str | None = None
    flags: tuple[str, ...] = ()
    width: int = 0
    operands: tuple[tuple[str, int], ...] = ()  # each operand's token and width


@dataclass
class Function:
    name: str
    header: str
    blocks: list[tuple[str | None, list[Inst]]]
    defs: dict[str, Inst] = field(default_factory=dict)

    @property
    def lines(self) -> list[Inst]:
        return [i for _, insts in self.blocks for i in insts]


def strip_comment(line: str) -> str:
    """A line without its trailing comment. A `;` inside a quoted name stays."""
    out, quoted = [], False
    for ch in line:
        if ch == '"':
            quoted = not quoted
        if ch == ";" and not quoted:
            break
        out.append(ch)
    return "".join(out).rstrip()


def instruction(text: str) -> Inst:
    """One instruction line, looked into if the format has it."""
    inst = Inst(text)
    m = ASSIGN.fullmatch(text)
    if not m:
        return inst
    inst.name, body = m[1], m[2]
    if b := BINARY.fullmatch(body):
        inst.op, inst.width = b[1], int(b[3])
        inst.flags = tuple(sorted(b[2].split()))
        inst.operands = ((b[4], inst.width), (b[5], inst.width))
    elif b := ICMP.fullmatch(body):
        inst.op, inst.width = f"icmp.{b[2]}", 1
        inst.flags = ("samesign",) if b[1] else ()
        inst.operands = ((b[4], int(b[3])), (b[5], int(b[3])))
    elif b := SELECT.fullmatch(body):
        if b[2] == b[4]:
            inst.op, inst.width = "select", int(b[2])
            inst.operands = ((b[1], 1), (b[3], inst.width), (b[5], inst.width))
    elif b := CAST.fullmatch(body):
        inst.op, inst.width = b[1], int(b[5])
        inst.flags = tuple(sorted(b[2].split()))
        inst.operands = ((b[4], int(b[3])),)
    elif b := CALL.fullmatch(body):
        op = INTRINSICS.get(b[2])
        args = [(a[1], int(a[0])) for a in ARGUMENT.findall(b[4])]
        if op is not None and b[1] == b[3]:
            info = lang.OPS[op]
            if b[2] in BOOL_FLAG:
                if len(args) == 2 and args[1][1] == 1 and args[1][0] in ("true", "false"):
                    inst.flags = (BOOL_FLAG[b[2]],) if args[1][0] == "true" else ()
                    args = args[:1]
                else:
                    args = []
            if len(args) == info.arity and all(w == int(b[1]) for _, w in args):
                inst.op, inst.width, inst.operands = op, int(b[1]), tuple(args)
    if inst.op is not None and any(f not in lang.OPS[inst.op].flags for f in inst.flags):
        inst.op = None
    return inst


def functions(module: str) -> list[Function]:
    """The functions a module defines, each line of each block as an `Inst`."""
    out: list[Function] = []
    current: Function | None = None
    for raw in module.splitlines():
        line = strip_comment(raw).strip()
        if current is None:
            m = DEFINE.match(line)
            if m and line.endswith("{"):
                current = Function(m[1], line, [(None, [])])
            continue
        if line == "}":
            out.append(current)
            current = None
        elif not line:
            continue
        elif (label := LABEL.fullmatch(line)) and not raw.startswith("  "):
            if current.blocks == [(None, [])]:
                current.blocks = []
            current.blocks.append((label[1], []))
        else:
            inst = instruction(line)
            current.blocks[-1][1].append(inst)
            if inst.name is not None:
                if inst.name in current.defs:
                    raise IRError(f"{inst.name} is defined twice in @{current.name}")
                current.defs[inst.name] = inst
    if current is not None:
        raise IRError(f"@{current.name} doesn't end")
    return out


def preamble(module: str) -> str:
    """The module's `target` lines, which a slice keeps, so it's checked for the same target."""
    return "".join(f"{line}\n" for line in module.splitlines() if line.startswith("target "))


# ------------------------------------------------------------------------------------------------------------
# Terms


def constant(token: str, width: int) -> Term:
    value = {"true": 1, "false": 0}.get(token)
    return ("const", (int(token) if value is None else value) & lang.mask(width), width)


def width_of(t: Term) -> int:
    return t[3] if t[0] == "op" else t[2]


def followed(inst: Inst | None) -> bool:
    """Whether a cut looks into an instruction: one the format has, that can't be undefined."""
    return inst is not None and inst.op is not None and not lang.OPS[inst.op].div


def members(f: Function, root: str, depth: int | None) -> dict[str, int]:
    """The instructions of the cut around `root`: those it reads within `depth` instructions, `root` at 1,
    through instructions a cut looks into. Each with its distance. No bound if `depth` is None."""
    found: dict[str, int] = {}
    frontier = [root]
    level = 1
    while frontier and (depth is None or level <= depth):
        following: list[str] = []
        for name in frontier:
            if name in found or not followed(f.defs.get(name)):
                continue
            found[name] = level
            following += [token for token, _ in f.defs[name].operands if token.startswith("%")]
        frontier = following
        level += 1
    return found


def term(f: Function, token: str, width: int, cut: dict[str, int]) -> Term:
    """An operand as a term: a constant, an instruction of the cut by what it computes, or a leaf."""
    if not token.startswith("%"):
        return constant(token, width)
    if token not in cut:
        return ("leaf", token, width)
    inst = f.defs[token]
    assert inst.op is not None
    args = tuple(term(f, t, w, cut) for t, w in inst.operands)
    return ("op", inst.op, inst.flags, inst.width, args)


def leaves(t: Term, out: dict[str, int] | None = None) -> dict[str, int]:
    """A term's leaves and their widths, in the order it reaches them."""
    out = {} if out is None else out
    if t[0] == "leaf":
        out.setdefault(t[1], t[2])
    elif t[0] == "op":
        for a in t[4]:
            leaves(a, out)
    return out


def subterms(t: Term, out: list[Term] | None = None, seen: set[Term] | None = None) -> list[Term]:
    """Every instruction in a term, once each, the term itself first."""
    out = [] if out is None else out
    seen = set() if seen is None else seen
    if t[0] == "op" and t not in seen:
        seen.add(t)
        out.append(t)
        for a in t[4]:
            subterms(a, out, seen)
    return out


def size(t: Term) -> int:
    """How many instructions a term takes."""
    return len(subterms(t))


def replace(t: Term, old: Term, new: Term) -> Term:
    """`t` with `old` replaced by `new`, wherever it is: one instruction has one value."""
    if t == old:
        return new
    if t[0] != "op":
        return t
    args = tuple(replace(a, old, new) for a in t[4])
    return t if args == t[4] else (*t[:4], args)


def substitute(t: Term, values: dict[str, Term]) -> Term:
    """`t` with each leaf named in `values` replaced by its term."""
    if t[0] == "leaf":
        return values.get(t[1], t)
    if t[0] != "op":
        return t
    args = tuple(substitute(a, values) for a in t[4])
    return t if args == t[4] else (*t[:4], args)


# ------------------------------------------------------------------------------------------------------------
# Printing


def literal(value: int, width: int) -> str:
    if width == 1:
        return "true" if value else "false"
    return str(lang.signed(value, width))


FLAG_ORDER = ("nuw", "nsw", "exact", "disjoint", "nneg", "samesign")


def print_inst(name: str, t: Term, operand: list[str]) -> str:
    """One instruction computing `t`, whose operands are already named in `operand`."""
    _, op, flags, width, args = t
    info = lang.OPS[op]
    widths = [width_of(a) for a in args]
    marks = "".join(f" {f}" for f in FLAG_ORDER if f in flags)
    if info.kind == "bin":
        return f"{name} = {info.llvm}{marks} i{width} {operand[0]}, {operand[1]}"
    if info.kind == "icmp":
        return f"{name} = icmp{marks} {info.llvm} i{widths[0]} {operand[0]}, {operand[1]}"
    if info.kind == "select":
        return f"{name} = select i1 {operand[0]}, i{width} {operand[1]}, i{width} {operand[2]}"
    if info.kind == "cast":
        return f"{name} = {info.llvm}{marks} i{widths[0]} {operand[0]} to i{width}"
    given = [f"i{width} {o}" for o in operand]
    if info.llvm in BOOL_FLAG:
        given.append("i1 true" if BOOL_FLAG[info.llvm] in flags else "i1 false")
    return f"{name} = call i{width} @llvm.{info.llvm}.i{width}({', '.join(given)})"


def declaration(t: Term) -> str | None:
    """The `declare` an intrinsic's call needs."""
    info = lang.OPS[t[1]]
    if info.kind != "intr":
        return None
    width = t[3]
    types = [f"i{width}"] * info.arity + (["i1"] if info.llvm in BOOL_FLAG else [])
    return f"declare i{width} @llvm.{info.llvm}.i{width}({', '.join(types)})"


def declarations(f: Function, names: list[str | None]) -> list[str]:
    """The declarations the instructions `names` of `f` need."""
    out: list[str] = []
    for name in names:
        inst = f.defs.get(name or "")
        if inst is not None and inst.op is not None:
            d = declaration(("op", inst.op, inst.flags, inst.width, ()))
            if d and d not in out:
                out.append(d)
    return out


def body(
    t: Term, prefix: str = "%t", known: dict[Term, str] | None = None, taken: Iterable[str] = ()
) -> tuple[list[str], str, list[str]]:
    """Instructions computing `t`, operands before the instructions that read them, and the value they end
    with. An instruction in `known` isn't computed again: its name is used. Also the declarations they
    need. A new instruction's name is none of `taken`, such as the function's parameters, `t`'s leaves or
    `known`'s names."""
    names: dict[Term, str] = dict(known or {})
    reserved = {*taken, *leaves(t), *names.values()}
    lines: list[str] = []
    declares: list[str] = []
    counter = 0

    def value(t: Term) -> str:
        nonlocal counter
        if t[0] == "leaf":
            return t[1]
        if t[0] == "const":
            return literal(t[1], t[2])
        if t in names:
            return names[t]
        operand = [value(a) for a in t[4]]
        while f"{prefix}{counter}" in reserved:
            counter += 1
        names[t] = f"{prefix}{counter}"
        counter += 1
        lines.append(print_inst(names[t], t, operand))
        d = declaration(t)
        if d and d not in declares:
            declares.append(d)
        return names[t]

    return lines, value(t), declares


def state(name: str, params: dict[str, int], t: Term) -> tuple[str, list[str]]:
    """A function `@name` of `params` that computes `t` and returns it, and the declarations it needs."""
    lines, value, declares = body(t, taken=params)
    given = ", ".join(f"i{w} {p}" for p, w in params.items())
    text = f"define i{width_of(t)} @{name}({given}) {{\n" + "".join(f"  {line}\n" for line in lines)
    return text + f"  ret i{width_of(t)} {value}\n}}\n", declares


def verbatim(
    name: str, params: dict[str, int], f: Function, cut: dict[str, int], root: str
) -> tuple[str, list[str]]:
    """The cut around `root` as a function `@name` of its leaves: the function's own lines, each after the
    instructions of the cut it reads, and otherwise in the function's order. A function's blocks needn't be
    written in the order they run, so its own order isn't always one a single block can have."""
    inst = f.defs[root]
    ordered: list[str] = []

    def place(token: str) -> None:
        if token in cut and token not in ordered:
            for operand, _ in f.defs[token].operands:
                place(operand)
            ordered.append(token)

    for i in f.lines:
        if i.name in cut:
            place(i.name)
    lines = [f.defs[token].text for token in ordered]
    declares = declarations(f, list(ordered))
    given = ", ".join(f"i{w} {p}" for p, w in params.items())
    text = f"define i{inst.width} @{name}({given}) {{\n" + "".join(f"  {line}\n" for line in lines)
    return text + f"  ret i{inst.width} {root}\n}}\n", declares


def renamed(header: str, old: str, new: str) -> str:
    """A `define` line with the function's name changed."""
    at = header.index(f"@{old}(")
    return header[:at] + f"@{new}(" + header[at + len(old) + 2 :]


def one_block(f: Function) -> tuple[str, int] | None:
    """If `f` is one block of instructions a cut looks into, ending in `ret` of an integer: what it returns,
    and its width."""
    if len(f.blocks) != 1 or not f.blocks[0][1]:
        return None
    *rest, last = f.blocks[0][1]
    m = RET.fullmatch(last.text)
    if not m or any(not followed(i) for i in rest):
        return None
    return m[2], int(m[1])


def rewritten(f: Function, root: str, cut: dict[str, int], final: Term) -> str:
    """`f` with `root` replaced by `final`: the new instructions before `root`, each use of `root` now a use
    of the new value, and every instruction of the cut nothing reads any more removed. A new value's name is
    none the function has: a parameter's, an instruction's or a block's, which share one namespace."""
    known = {term(f, name, f.defs[name].width, cut): name for name in cut if name != root}
    stem = re.sub(r"[^-a-zA-Z$._0-9]", "_", root[1:])
    taken = {*re.findall(NAME, f.header), *f.defs, *(f"%{label}" for label, _ in f.blocks if label)}
    lines, value, _ = body(final, prefix=f"%{stem}.rs", known=known, taken=taken)
    use = re.compile(re.escape(root) + r"(?![-a-zA-Z$._0-9\"])")
    out: list[tuple[str | None, list[str]]] = []
    for label, insts in f.blocks:
        texts: list[str] = []
        for inst in insts:
            if inst.name == root:
                texts += lines
            else:
                texts.append(use.sub(lambda _: value, inst.text))
        out.append((label, texts))
    # Remove what's dead of the cut: an instruction of it whose name no other line reads.
    removable = {name for name in cut if name != root}
    changed = True
    while changed:
        changed = False
        everything = "\n".join(t for _, texts in out for t in texts)
        for name in sorted(removable):
            uses = len(re.findall(re.escape(name) + r"(?![-a-zA-Z$._0-9\"])", everything))
            if uses == 1:
                removable.discard(name)
                out = [(label, [t for t in texts if not t.startswith(f"{name} = ")]) for label, texts in out]
                changed = True
                break
    text = f.header + "\n"
    for i, (label, texts) in enumerate(out):
        if label is not None:
            text += ("\n" if i else "") + f"{label}:\n"
        text += "".join(f"  {t}\n" for t in texts)
    return text + "}\n"
