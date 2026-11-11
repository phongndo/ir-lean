"""The rule format: one declarative source a rule, and the two things generated from it.

A rule is a pattern, a replacement and side conditions, as S-expressions over LLVM's scalar integer
instructions. docs/rules.md has the format. From one parsed `Rule` come:

- `Rule.statement`, the Lean proposition `Rules.Stmt.<name>`: the replacement refines the pattern, for every
  width, operand, open flag and constant meeting the side conditions;
- `Rule.match` and `Rule.build`, the matcher: whether the pattern matches a term of real IR, and the
  replacement it gives there.

Neither is trusted. A certificate proves each application again from the rule's theorem, so a statement that
isn't the pattern's, or a matcher that matches something else, shows as a proof that fails.

Terms of real IR, which the matcher runs on, are tuples, equal when they're the same computation:

    ("leaf", name, width)                 an argument, or an instruction the cut doesn't look into
    ("const", value, width)               a ConstantInt, `value` unsigned
    ("op", op, flags, width, args)        an instruction: `op` a key of OPS, `flags` the sorted flags it has
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Any

Term = tuple[Any, ...]


class RuleError(ValueError):
    """A rule the format can't hold, or that isn't well formed."""


@dataclass(frozen=True)
class OpInfo:
    """One instruction the format knows: its Lean function, how many operands it takes, its flags in the order
    Lean takes them, and how LLVM prints it."""

    lean: str
    arity: int
    flags: tuple[str, ...]
    kind: str  # bin, icmp, select, cast or intr
    llvm: str
    div: bool = False

    @property
    def mono(self) -> str:
        """The congruence lemma for it in rules/Rules/Mono.lean."""
        return "Rules.Mono." + self.lean.rsplit(".", 1)[-1]


def _ops() -> dict[str, OpInfo]:
    ops: dict[str, OpInfo] = {}
    for name in ("add", "sub", "mul", "shl"):
        ops[name] = OpInfo(f"Val.{name}", 2, ("nuw", "nsw"), "bin", name)
    for name in ("lshr", "ashr"):
        ops[name] = OpInfo(f"Val.{name}", 2, ("exact",), "bin", name)
    for name in ("udiv", "sdiv"):
        ops[name] = OpInfo(f"Val.{name}", 2, ("exact",), "bin", name, div=True)
    for name in ("urem", "srem"):
        ops[name] = OpInfo(f"Val.{name}", 2, (), "bin", name, div=True)
    ops["and"] = OpInfo("Val.and", 2, (), "bin", "and")
    ops["xor"] = OpInfo("Val.xor", 2, (), "bin", "xor")
    ops["or"] = OpInfo("Val.or", 2, ("disjoint",), "bin", "or")
    for pred in ("eq", "ne", "ult", "ule", "ugt", "uge", "slt", "sle", "sgt", "sge"):
        ops[f"icmp.{pred}"] = OpInfo(f"Val.icmp{pred.capitalize()}", 2, ("samesign",), "icmp", pred)
    ops["select"] = OpInfo("select", 3, (), "select", "select")
    ops["zext"] = OpInfo("Val.zext", 1, ("nneg",), "cast", "zext")
    ops["sext"] = OpInfo("Val.sext", 1, (), "cast", "sext")
    ops["trunc"] = OpInfo("Val.trunc", 1, ("nuw", "nsw"), "cast", "trunc")
    for name in ("umin", "umax", "smin", "smax"):
        ops[name] = OpInfo(f"Val.{name}", 2, (), "intr", name)
    for name, lean in (
        ("uadd_sat", "uaddSat"),
        ("usub_sat", "usubSat"),
        ("sadd_sat", "saddSat"),
        ("ssub_sat", "ssubSat"),
    ):
        ops[name] = OpInfo(f"Val.{lean}", 2, (), "intr", name.replace("_", "."))
    for name in ("ctpop", "bitreverse", "bswap"):
        ops[name] = OpInfo(f"Val.{name}", 1, (), "intr", name)
    # Their second operand, an `i1` constant, is a flag here: `zp` is is_zero_poison, `imp` is_int_min_poison.
    ops["ctlz"] = OpInfo("Val.ctlz", 1, ("zp",), "intr", "ctlz")
    ops["cttz"] = OpInfo("Val.cttz", 1, ("zp",), "intr", "cttz")
    ops["abs"] = OpInfo("Val.abs", 1, ("imp",), "intr", "abs")
    ops["fshl"] = OpInfo("Val.fshl", 3, (), "intr", "fshl")
    ops["fshr"] = OpInfo("Val.fshr", 3, (), "intr", "fshr")
    return ops


OPS = _ops()

# Constant expressions: the Lean for each, over BitVec, and its arity.
CEXPRS: dict[str, tuple[str, int]] = {
    "c.not": ("~~~{0}", 1),
    "c.neg": ("-{0}", 1),
    "c.add": ("{0} + {1}", 2),
    "c.sub": ("{0} - {1}", 2),
    "c.and": ("{0} &&& {1}", 2),
    "c.or": ("{0} ||| {1}", 2),
    "c.xor": ("{0} ^^^ {1}", 2),
    "c.urem": ("{0} % {1}", 2),
    "c.srem": ("{0}.srem {1}", 2),
}

# Side conditions: the Lean for each, and its arity. `wgt` takes a number, not an expression.
CONDS: dict[str, tuple[str, int]] = {
    "eq": ("{0} = {1}", 2),
    "ne": ("{0} ≠ {1}", 2),
    "ult": ("{0} < {1}", 2),
    "ule": ("{0} ≤ {1}", 2),
    "bule": ("{0}.ule {1} = true", 2),
    "bsle": ("{0}.sle {1} = true", 2),
    "pow2": ("{0}.toNat.isPowerOfTwo", 1),
    "msb": ("{0}.msb = true", 1),
    "lsb": ("{0}.getLsbD 0 = true", 1),
}

# Names a rule's variables can't take once lowercased: Lean's keywords, and the binders the statement makes
# itself.
LEAN_WORDS = frozenset(
    "abbrev at axiom by calc class def deriving do else end example export extends for fun have if import in "
    "infix inductive instance let local macro match mutual namespace notation open partial private "
    "protected section set_option show structure suffices syntax then theorem this universe variable where "
    "with from some none true false w".split()
)
MADE = re.compile(r"(w|f|q|h)\d+")


@dataclass(frozen=True)
class Var:
    name: str
    width: int | None = None


@dataclass(frozen=True)
class CVar:
    name: str


@dataclass(frozen=True)
class Lit:
    value: int | str


@dataclass(frozen=True)
class App:
    op: str
    flags: tuple[str, ...]
    args: tuple[Any, ...]


@dataclass(frozen=True)
class Bind:
    name: str
    term: Any


@dataclass(frozen=True)
class CExpr:
    op: str
    args: tuple[Any, ...]


@dataclass(frozen=True)
class Cond:
    op: str
    args: tuple[Any, ...]


@dataclass
class Typed:
    """A node with the class of its width, and its operands the same way."""

    node: Any
    cls: int
    kids: list[Typed] = field(default_factory=list)


class Widths:
    """Width classes, unified as the instructions require. A class is a number, or a variable."""

    def __init__(self) -> None:
        self.parent: list[int] = []
        self.number: list[int | None] = []

    def new(self, number: int | None = None) -> int:
        self.parent.append(len(self.parent))
        self.number.append(number)
        return len(self.parent) - 1

    def find(self, i: int) -> int:
        while self.parent[i] != i:
            self.parent[i] = self.parent[self.parent[i]]
            i = self.parent[i]
        return i

    def union(self, a: int, b: int) -> None:
        a, b = self.find(a), self.find(b)
        if a == b:
            return
        na, nb = self.number[a], self.number[b]
        if na is not None and nb is not None and na != nb:
            raise RuleError(f"an operand would have to be both i{na} and i{nb}")
        self.parent[b] = a
        if na is None:
            self.number[a] = nb


# ------------------------------------------------------------------------------------------------------------
# Reading S-expressions

TOKEN = re.compile(r"\s*(\(|\)|[^\s()]+)")
VAR = re.compile(r"([A-Z][A-Za-z0-9_]*)(?::(\d+))?")
CVAR = re.compile(r"C\d*")
INT = re.compile(r"-?\d+")


def sexpr(text: str) -> Any:
    """`text` as nested lists of atoms."""
    tokens = TOKEN.findall(text)
    if "".join(tokens) != "".join(text.split()):
        raise RuleError(f"can't read {text!r}")
    position = 0

    def read() -> Any:
        nonlocal position
        if position >= len(tokens):
            raise RuleError(f"{text!r} ends early")
        token = tokens[position]
        position += 1
        if token == ")":
            raise RuleError(f"{text!r} has a `)` with no `(`")
        if token != "(":
            return token
        items = []
        while position < len(tokens) and tokens[position] != ")":
            items.append(read())
        if position >= len(tokens):
            raise RuleError(f"{text!r} has a `(` with no `)`")
        position += 1
        if not items:
            raise RuleError(f"{text!r} has an empty `()`")
        return items

    out = read()
    if position != len(tokens):
        raise RuleError(f"{text!r} has something after its end")
    return out


def atom(token: str) -> Any:
    if INT.fullmatch(token):
        return Lit(int(token))
    if token in ("intmin", "intmax"):
        return Lit(token)
    m = VAR.fullmatch(token)
    if not m:
        raise RuleError(f"{token!r} isn't a variable, a constant or a number")
    if CVAR.fullmatch(m[1]):
        if m[2]:
            raise RuleError(f"{token!r}: a constant takes its operand's width")
        return CVar(m[1])
    return Var(m[1], int(m[2]) if m[2] else None)


def term(sx: Any) -> Any:
    """A pattern or replacement term."""
    if isinstance(sx, str):
        return atom(sx)
    head, rest = sx[0], sx[1:]
    if not isinstance(head, str):
        raise RuleError(f"{head!r} isn't an instruction")
    if head == "bind":
        if len(rest) != 2 or not isinstance(rest[0], str) or not isinstance(atom(rest[0]), Var):
            raise RuleError("`bind` takes a name and a term")
        return Bind(rest[0], term(rest[1]))
    if head in CEXPRS:
        if len(rest) != CEXPRS[head][1]:
            raise RuleError(f"{head} takes {CEXPRS[head][1]} operands")
        args = tuple(term(a) for a in rest)
        for a in args:
            if not isinstance(a, CVar | Lit | CExpr):
                raise RuleError(f"{head} is over constants, and {a} isn't one")
        return CExpr(head, args)
    parts = head.split(".")
    op = ".".join(parts[:2]) if parts[0] == "icmp" else parts[0]
    flags = tuple(parts[2:] if parts[0] == "icmp" else parts[1:])
    info = OPS.get(op)
    if info is None:
        raise RuleError(f"{head!r} isn't an instruction the format has")
    for flag in flags:
        if flag not in info.flags:
            raise RuleError(f"{op} has no flag {flag!r}")
    if len(set(flags)) != len(flags):
        raise RuleError(f"{head!r} names a flag twice")
    if len(rest) != info.arity:
        raise RuleError(f"{op} takes {info.arity} operands, not {len(rest)}")
    return App(op, tuple(f for f in info.flags if f in flags), tuple(term(a) for a in rest))


def cond(sx: Any) -> Cond:
    if isinstance(sx, str):
        raise RuleError(f"{sx!r} isn't a side condition")
    head, rest = sx[0], sx[1:]
    if head == "not":
        if len(rest) != 1:
            raise RuleError("`not` takes one condition")
        return Cond("not", (cond(rest[0]),))
    if head == "wgt":
        if len(rest) != 1 or not isinstance(rest[0], str) or not rest[0].isdigit():
            raise RuleError("`wgt` takes a number")
        return Cond("wgt", (int(rest[0]),))
    if head not in CONDS:
        raise RuleError(f"{head!r} isn't a side condition")
    if len(rest) != CONDS[head][1]:
        raise RuleError(f"{head} takes {CONDS[head][1]} operands")
    args = tuple(term(a) for a in rest)
    for a in args:
        if not isinstance(a, CVar | Lit | CExpr):
            raise RuleError(f"a side condition is over constants, and {a} isn't one")
    return Cond(head, args)


def show(node: Any) -> str:
    """A term or condition, as the format writes it."""
    if isinstance(node, Var):
        return node.name + (f":{node.width}" if node.width is not None else "")
    if isinstance(node, CVar):
        return node.name
    if isinstance(node, Lit):
        return str(node.value)
    if isinstance(node, App):
        return "(" + " ".join([".".join([node.op, *node.flags]), *(show(a) for a in node.args)]) + ")"
    if isinstance(node, Bind):
        return f"(bind {node.name} {show(node.term)})"
    if isinstance(node, CExpr | Cond):
        return (
            "("
            + " ".join([node.op, *(show(a) if not isinstance(a, int) else str(a) for a in node.args)])
            + ")"
        )
    raise RuleError(f"can't show {node!r}")


# ------------------------------------------------------------------------------------------------------------
# Constants


def mask(width: int) -> int:
    return (1 << width) - 1


def literal(value: int | str, width: int) -> int:
    """A literal at a width, unsigned: what `literal_lean` denotes."""
    if value == "intmin":
        return (1 << (width - 1)) if width else 0
    if value == "intmax":
        return ((1 << (width - 1)) - 1) if width else 0
    assert isinstance(value, int)
    return value & mask(width)


def literal_lean(value: int | str, width: str) -> str:
    if value == "intmin":
        return f"BitVec.intMin {width}"
    if value == "intmax":
        return f"BitVec.intMax {width}"
    assert isinstance(value, int)
    if value == -1:
        return f"BitVec.allOnes {width}"
    if value < 0:
        return f"BitVec.ofInt {width} ({value})"
    return f"{value}#{width}"


def signed(value: int, width: int) -> int:
    return value - (1 << width) if width and value >> (width - 1) else value


def cexpr_value(op: str, args: list[int], width: int) -> int:
    """A constant expression's value, as Lean's `BitVec` computes it."""
    m = mask(width)
    if op == "c.not":
        return ~args[0] & m
    if op == "c.neg":
        return -args[0] & m
    a, b = args
    if op == "c.add":
        return (a + b) & m
    if op == "c.sub":
        return (a - b) & m
    if op == "c.and":
        return a & b
    if op == "c.or":
        return a | b
    if op == "c.xor":
        return a ^ b
    if op == "c.urem":
        return a % b if b else a
    if op == "c.srem":
        sa, sb = signed(a, width), signed(b, width)
        if sb == 0:
            return a
        r = abs(sa) % abs(sb)
        return (-r if sa < 0 else r) & m
    raise RuleError(f"{op} isn't a constant expression")


# ------------------------------------------------------------------------------------------------------------
# A rule


@dataclass
class Match:
    """What a pattern bound in a term: each variable's term, each constant's value, and each width class."""

    values: dict[str, Term] = field(default_factory=dict)
    consts: dict[str, int] = field(default_factory=dict)
    widths: dict[int, int] = field(default_factory=dict)


class Rule:
    """One parsed rule. `raw` is its JSON object."""

    def __init__(self, raw: dict[str, Any]) -> None:
        known = {"name", "match", "replace", "where", "doc", "from", "sites"}
        if not isinstance(raw, dict) or set(raw) - known:
            raise RuleError(f"a rule has only {', '.join(sorted(known))}: {raw!r}")
        for key in ("name", "match", "replace"):
            if not isinstance(raw.get(key), str):
                raise RuleError(f"a rule needs `{key}`, a string: {raw!r}")
        self.name: str = raw["name"]
        if not re.fullmatch(r"[a-z][A-Za-z0-9_]*", self.name) or self.name in LEAN_WORDS:
            raise RuleError(f"{self.name!r} isn't a name a rule can take")
        self.doc: str = raw.get("doc", "")
        self.source: str | None = raw.get("from")
        self.sites: list[str] = list(raw.get("sites", []))
        try:
            self.pattern = term(sexpr(raw["match"]))
            self.replacement = term(sexpr(raw["replace"]))
            self.conds = [cond(sexpr(c)) for c in raw.get("where", [])]
            self._check()
            self._type()
        except RuleError as error:
            raise RuleError(f"{self.name}: {error}") from error

    # -- well-formedness

    def _check(self) -> None:
        if not isinstance(self.pattern, App):
            raise RuleError("the pattern has to be an instruction")
        self.values: list[str] = []  # variables and bound names, in the pattern's order
        self.consts: list[str] = []
        binds: set[str] = set()

        def walk(node: Any) -> None:
            if isinstance(node, Var):
                # A name `bind` gave an instruction, used again: the same instruction.
                if node.name not in binds and node.name not in self.values:
                    self.values.append(node.name)
            elif isinstance(node, CVar):
                if node.name not in self.consts:
                    self.consts.append(node.name)
            elif isinstance(node, Bind):
                if node.name in binds or node.name in self.values:
                    raise RuleError(f"{node.name} is bound twice")
                if not isinstance(node.term, App):
                    raise RuleError("`bind` names an instruction")
                binds.add(node.name)
                walk(node.term)
            elif isinstance(node, App | CExpr):
                for a in node.args:
                    walk(a)

        walk(self.pattern)
        self.binds = binds
        for name in [*self.values, *self.consts, *binds]:
            low = name.lower()
            if low in LEAN_WORDS or MADE.fullmatch(low):
                raise RuleError(f"{name} would be `{low}` in Lean, which is taken")
        lows = [n.lower() for n in [*self.values, *self.consts, *binds]]
        if len(set(lows)) != len(lows):
            raise RuleError("two variables differ only in case")

        def bound(node: Any, where: str) -> None:
            if isinstance(node, Var):
                if node.name not in self.values and node.name not in binds:
                    raise RuleError(f"{where} uses {node.name}, which the pattern doesn't bind")
                if node.width is not None:
                    raise RuleError(f"{where} can't give {node.name} a width")
            elif isinstance(node, CVar):
                if node.name not in self.consts:
                    raise RuleError(f"{where} uses {node.name}, which the pattern doesn't bind")
            elif isinstance(node, Bind):
                raise RuleError(f"{where} can't bind")
            elif isinstance(node, App):
                if OPS[node.op].div:
                    raise RuleError(f"{where} can't divide: {node.op}")
                for a in node.args:
                    bound(a, where)
            elif isinstance(node, CExpr | Cond):
                for a in node.args:
                    if not isinstance(a, int):
                        bound(a, where)

        bound(self.replacement, "the replacement")
        for c in self.conds:
            bound(c, "a side condition")

    # -- widths

    def _type(self) -> None:
        ws = Widths()
        self.ws = ws
        var_cls: dict[str, int] = {}
        self.bound_typed: dict[str, Typed] = {}
        self.casts: list[tuple[str, int, int]] = []  # cast, operand's class, result's class

        def ty(node: Any, pattern: bool) -> Typed:
            if isinstance(node, Var):
                if node.name in self.bound_typed:
                    return Typed(node, self.bound_typed[node.name].cls)
                if node.name not in var_cls:
                    var_cls[node.name] = ws.new()
                if node.width is not None:
                    ws.union(var_cls[node.name], ws.new(node.width))
                return Typed(node, var_cls[node.name])
            if isinstance(node, CVar):
                if node.name not in var_cls:
                    var_cls[node.name] = ws.new()
                return Typed(node, var_cls[node.name])
            if isinstance(node, Lit):
                return Typed(node, ws.new())
            if isinstance(node, Bind):
                inner = ty(node.term, pattern)
                self.bound_typed[node.name] = inner
                return Typed(node, inner.cls, [inner])
            kids = [ty(a, pattern) for a in node.args]
            if isinstance(node, CExpr):
                out = ws.new()
                for k in kids:
                    ws.union(out, k.cls)
                return Typed(node, out, kids)
            info = OPS[node.op]
            if info.kind == "icmp":
                ws.union(kids[0].cls, kids[1].cls)
                return Typed(node, ws.new(1), kids)
            if info.kind == "select":
                ws.union(kids[0].cls, ws.new(1))
                ws.union(kids[1].cls, kids[2].cls)
                return Typed(node, kids[1].cls, kids)
            if info.kind == "cast":
                out = ws.new()
                self.casts.append((node.op, kids[0].cls, out))
                return Typed(node, out, kids)
            out = kids[0].cls
            for k in kids[1:]:
                ws.union(out, k.cls)
            return Typed(node, out, kids)

        self.lhs = ty(self.pattern, True)
        self.rhs = ty(self.replacement, False)
        ws.union(self.lhs.cls, self.rhs.cls)
        self.typed_conds: list[tuple[Cond, list[Any]]] = []

        def ty_cond(c: Cond) -> list[Any]:
            if c.op == "not":
                return [ty_cond(c.args[0])]
            if c.op == "wgt":
                return []
            kids = [ty(a, False) for a in c.args]
            for k in kids[1:]:
                ws.union(kids[0].cls, k.cls)
            return kids

        for c in self.conds:
            self.typed_conds.append((c, ty_cond(c)))
        self.var_cls = var_cls
        # Name each class that isn't a number: the first the pattern reaches is `w`, then `w1`, `w2`.
        self.width_name: dict[int, str] = {}
        order: list[int] = []

        def visit(t: Typed) -> None:
            c = ws.find(t.cls)
            if c not in order:
                order.append(c)
            for k in t.kids:
                visit(k)

        visit(self.lhs)
        pattern_classes = set(order)
        visit(self.rhs)
        for _, kids in self.typed_conds:
            stack = list(kids)
            while stack:
                k = stack.pop()
                if isinstance(k, list):
                    stack.extend(k)
                else:
                    visit(k)
        if set(order) - pattern_classes:
            raise RuleError("the replacement or a side condition has a width the pattern doesn't fix")
        self.width_vars: list[str] = []
        self.w_class: int | None = None
        for c in order:
            if ws.number[c] is not None:
                self.width_name[c] = str(ws.number[c])
                continue
            if self.w_class is None:
                self.w_class = c
            self.width_name[c] = "w" if c == self.w_class else f"w{len(self.width_vars)}"
            self.width_vars.append(self.width_name[c])

    def width(self, t: Typed) -> str:
        return self.width_name[self.ws.find(t.cls)]

    @property
    def divides(self) -> bool:
        """Whether the pattern has a division, which a certificate can't follow yet."""

        def has(node: Any) -> bool:
            if isinstance(node, App):
                return OPS[node.op].div or any(has(a) for a in node.args)
            return isinstance(node, Bind) and has(node.term)

        return has(self.pattern)

    # -- the Lean statement

    def _cexpr_lean(self, t: Typed) -> str:
        node = t.node
        if isinstance(node, CVar):
            return node.name.lower()
        if isinstance(node, Lit):
            text = literal_lean(node.value, self.width(t))
            return f"({text})" if " " in text else text
        return "(" + CEXPRS[node.op][0].format(*(self._cexpr_lean(k) for k in t.kids)) + ")"

    def _cond_lean(self, c: Cond, kids: list[Any]) -> str:
        if c.op == "not":
            return "¬ " + self._cond_lean(c.args[0], kids[0])
        if c.op == "wgt":
            return f"{c.args[0]} < w"
        return CONDS[c.op][0].format(*(self._cexpr_lean(k) for k in kids))

    def lean(self) -> dict[str, Any]:
        """The statement's parts: its binders, in order, its hypotheses, and the two sides."""
        flags: list[str] = []
        # The variable a division below the root becomes, its hypothesis, and its width.
        divs: list[tuple[str, str, str]] = []
        bound: dict[str, str] = {}

        def pat(t: Typed, root: bool = False) -> str:
            node = t.node
            if isinstance(node, Var):
                return bound.get(node.name, node.name.lower())
            if isinstance(node, CVar | Lit | CExpr):
                return f"(some {self._cexpr_lean(t)})"
            if isinstance(node, Bind):
                bound[node.name] = pat(t.kids[0])
                return bound[node.name]
            info = OPS[node.op]
            taken = []
            for flag in info.flags:
                if flag in node.flags:
                    taken.append("true")
                else:
                    flags.append(f"f{len(flags)}")
                    taken.append(flags[-1])
            args = [pat(k) for k in t.kids]
            lead = [self.width(t)] if info.kind == "cast" else []
            text = " ".join([info.lean, *lead, *args, *taken])
            if info.div and not root:
                q = f"q{len(divs)}"
                divs.append((q, f"{text} = Outcome.ok {q}", self.width(t)))
                return q
            return f"({text})"

        def rep(t: Typed) -> str:
            node = t.node
            if isinstance(node, Var):
                return bound.get(node.name, node.name.lower())
            if isinstance(node, CVar | Lit | CExpr):
                return f"(some {self._cexpr_lean(t)})"
            info = OPS[node.op]
            taken = ["true" if flag in node.flags else "false" for flag in info.flags]
            lead = [self.width(t)] if info.kind == "cast" else []
            return "(" + " ".join([info.lean, *lead, *(rep(k) for k in t.kids), *taken]) + ")"

        left = pat(self.lhs, root=True)
        if not OPS[self.pattern.op].div:
            left = f"(Outcome.ok {left})"
        right = f"(Outcome.ok {rep(self.rhs)})"
        binders: list[tuple[str, str]] = []
        for name in self.values:
            binders.append((name.lower(), f"Val {self.width_name[self.ws.find(self.var_cls[name])]}"))
        for name in self.consts:
            binders.append((name.lower(), f"BitVec {self.width_name[self.ws.find(self.var_cls[name])]}"))
        for q, _, width in divs:
            binders.append((q, f"Val {width}"))
        for f in flags:
            binders.append((f, "Bool"))
        cast_hyps: list[str] = []
        for op, a, b in self.casts:
            wa, wb = self.width_name[self.ws.find(a)], self.width_name[self.ws.find(b)]
            hyp = f"{wb} < {wa}" if op == "trunc" else f"{wa} < {wb}"
            if hyp not in cast_hyps:
                cast_hyps.append(hyp)
        conds = [self._cond_lean(c, kids) for c, kids in self.typed_conds]
        return {
            "widths": self.width_vars,
            "binders": binders,
            "casts": cast_hyps,
            "divs": [h for _, h, _ in divs],
            "conds": conds,
            "left": left,
            "right": right,
        }

    def statement(self) -> str:
        """The proposition, as Lean: `∀ ..., hypotheses → Refines left right`."""
        parts = self.lean()
        groups: list[str] = []
        if parts["widths"]:
            groups.append("{" + " ".join(parts["widths"]) + " : Nat}")
        run: list[str] = []
        kind = ""
        for name, ty in [*parts["binders"], ("", "")]:
            if ty != kind and run:
                groups.append(f"({' '.join(run)} : {kind})")
                run = []
            kind = ty
            if name:
                run.append(name)
        lines = []
        line = "  ∀"
        for g in groups:
            if len(line) + 1 + len(g) > 116:
                lines.append(line)
                line = "     "
            line += " " + g
        lines.append(line + ",")
        for h in [*parts["casts"], *parts["divs"], *parts["conds"]]:
            lines.append(f"    {h} →")
        tail = f"    Refines {parts['left']} {parts['right']}"
        if len(tail) > 118:
            lines.append(f"    Refines {parts['left']}")
            lines.append(f"      {parts['right']}")
        else:
            lines.append(tail)
        return "\n".join(lines)

    def instance(self, divs: list[str] | None = None) -> str:
        """The rule's theorem applied at one place: every operand, flag and constant left for Lean to read off
        the goal, each cast's and side condition's hypothesis decided, and `divs` the proofs that each
        division
        below the root returned."""
        parts = self.lean()
        args = ["_"] * len(parts["binders"]) + ["(by decide)"] * len(parts["casts"])
        args += list(divs or [])
        if len(divs or []) != len(parts["divs"]):
            raise RuleError(f"{self.name} needs {len(parts['divs'])} divisions' results")
        args += ["(by decide)"] * len(parts["conds"])
        return " ".join([f"Rules.{self.name}", *args])

    # -- the matcher

    def _const_value(self, t: Typed, m: Match) -> int | None:
        """A constant expression's value under `m`, or None if a constant in it isn't bound yet."""
        node = t.node
        width = m.widths.get(self.ws.find(t.cls))
        if width is None:
            return None
        if isinstance(node, CVar):
            return m.consts.get(node.name)
        if isinstance(node, Lit):
            return literal(node.value, width)
        args = [self._const_value(k, m) for k in t.kids]
        if any(a is None for a in args):
            return None
        return cexpr_value(node.op, [a for a in args if a is not None], width)

    def _cond_holds(self, c: Cond, kids: list[Any], m: Match) -> bool:
        if c.op == "not":
            return not self._cond_holds(c.args[0], kids[0], m)
        if c.op == "wgt":
            return self.w_class is not None and m.widths[self.w_class] > c.args[0]
        values = [self._const_value(k, m) for k in kids]
        if any(v is None for v in values):
            return False
        width = m.widths[self.ws.find(kids[0].cls)]
        a = values[0]
        assert a is not None
        if c.op == "pow2":
            return a != 0 and a & (a - 1) == 0
        if c.op == "msb":
            return width > 0 and bool(a >> (width - 1))
        if c.op == "lsb":
            return bool(a & 1)
        b = values[1]
        assert b is not None
        if c.op == "bsle":
            return signed(a, width) <= signed(b, width)
        return {"eq": a == b, "ne": a != b, "ult": a < b, "ule": a <= b, "bule": a <= b}[c.op]

    def match(self, t: Term) -> Match | None:
        """What the pattern binds in `t`, with every side condition holding, or None."""
        m = Match()
        later: list[tuple[Typed, Term]] = []

        def width(p: Typed, t: Term) -> bool:
            c = self.ws.find(p.cls)
            number = self.ws.number[c]
            if number is not None and number != t[2 if t[0] != "op" else 3]:
                return False
            return m.widths.setdefault(c, t[2 if t[0] != "op" else 3]) == t[2 if t[0] != "op" else 3]

        def go(p: Typed, t: Term) -> bool:
            node = p.node
            if not width(p, t):
                return False
            if isinstance(node, Var):
                return m.values.setdefault(node.name, t) == t
            if isinstance(node, CVar):
                return t[0] == "const" and m.consts.setdefault(node.name, t[1]) == t[1]
            if isinstance(node, Lit):
                return t[0] == "const" and t[1] == literal(node.value, t[2])
            if isinstance(node, CExpr):
                if t[0] != "const":
                    return False
                later.append((p, t))
                return True
            if isinstance(node, Bind):
                if not go(p.kids[0], t):
                    return False
                m.values[node.name] = t
                return True
            if t[0] != "op" or t[1] != node.op or any(f not in t[2] for f in node.flags):
                return False
            return len(t[4]) == len(p.kids) and all(go(k, a) for k, a in zip(p.kids, t[4], strict=True))

        if not go(self.lhs, t):
            return None
        for p, c in later:
            if self._const_value(p, m) != c[1]:
                return None
        # A cast's operand is narrower or wider than its result, as the verifier has it.
        for op, a, b in self.casts:
            wa, wb = m.widths.get(self.ws.find(a)), m.widths.get(self.ws.find(b))
            if wa is None or wb is None or (wb >= wa if op == "trunc" else wa >= wb):
                return None
        for c, kids in self.typed_conds:
            if not self._cond_holds(c, kids, m):
                return None
        return m

    def build(self, m: Match) -> Term:
        """The replacement, for what the pattern bound."""

        def go(t: Typed) -> Term:
            node = t.node
            width = m.widths[self.ws.find(t.cls)]
            if isinstance(node, Var):
                return m.values[node.name]
            if isinstance(node, CVar | Lit | CExpr):
                value = self._const_value(t, m)
                assert value is not None
                return ("const", value, width)
            return ("op", node.op, tuple(sorted(node.flags)), width, tuple(go(k) for k in t.kids))

        return go(self.rhs)

    def apply(self, t: Term) -> Term | None:
        """The replacement for `t`, if the rule applies to it."""
        m = self.match(t)
        return None if m is None else self.build(m)


def load(raw: dict[str, Any]) -> list[Rule]:
    """The rules of one source file, in its order."""
    if not isinstance(raw, dict) or not isinstance(raw.get("rules"), list):
        raise RuleError("a rule file has `rules`, a list")
    rules = [Rule(r) for r in raw["rules"]]
    names = [r.name for r in rules]
    if len(set(names)) != len(names):
        raise RuleError("two rules have one name")
    return rules
