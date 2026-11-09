#!/usr/bin/env python3
"""The rewrites in chunk 1's peephole passes, InstSimplify, InstCombine, AggressiveInstCombine and
Reassociate, at the pinned LLVM: INV-04 for chunk 1. docs/rewrite-inventory.md states the rule for where
one rewrite ends and the next begins, and what this doesn't see.

Each rewrite is a *site* in the pinned C++: a statement where a fold function commits a change. A fold is
a function that can decline, with a null result or a false flag, and is an entry point, is forwarded to by
a fold, or builds IR. A site is a return of a value or of `true` that isn't a forward of another fold's
result, or an assignment of `true` to a changed flag. Each site gets a stable ID, its file and line, the
function it's in, the comment above it, and what it needs from the model: integers only, or floating
point, memory or calls, each of which another lane's work has to land first.

The inventory is in tests/llvm_scope/rewrites/, one file per pass. `check` derives it again from the
pinned source and fails if a rewrite appeared, disappeared or changed without the files changing.

usage:
  tests/llvm_rewrites.py generate        write tests/llvm_scope/rewrites/*.json from $LLVM_PROJECT_SRC
  tests/llvm_rewrites.py check           derive them again and fail on any difference
  tests/llvm_rewrites.py summary [--json] the totals, by pass and by what each rewrite needs, from the files

`generate` and `check` need the dev shell, for LLVM_PROJECT_SRC. `summary` reads only the files in the
repo."""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
sys.path.append(str(ROOT / "tools"))
from irlean import hashing, pins, schemas  # noqa: E402

HERE = ROOT / "tests" / "llvm_scope" / "rewrites"

# The files each pass's rewrites are written in, under llvm/. A pass's rewrites are the sites in its own
# files:
# InstCombine also calls InstSimplify's folds, and those are counted once, under InstSimplify.
PASSES: dict[str, dict[str, Any]] = {
    "instsimplify": {
        "prefix": "IS",
        "files": ["lib/Analysis/InstructionSimplify.cpp", "lib/Transforms/Scalar/InstSimplifyPass.cpp"],
        # simplifyInstruction is what the pass calls on each instruction. Every other function
        # InstructionSimplify.cpp
        # exports is called by other passes, InstCombine among them, so each is an entry too.
        "entries": ["simplifyInstruction", "runImpl", "@exported"],
    },
    "instcombine": {
        "prefix": "IC",
        "files": "lib/Transforms/InstCombine/*.cpp",
        # The InstVisitor dispatches to each visit method, which the scanner can't follow, so each is an
        # entry.
        "entries": [
            "@visit",
            "InstCombinerImpl::run",
            "InstCombinerImpl::prepareWorklist",
            "InstCombinePass::run",
            "combineInstructionsOverFunction",
        ],
    },
    "aggressive-instcombine": {
        "prefix": "AIC",
        "files": "lib/Transforms/AggressiveInstCombine/*.cpp",
        "entries": ["runImpl", "AggressiveInstCombinePass::run", "TruncInstCombine::run"],
    },
    "reassociate": {
        "prefix": "RA",
        "files": ["lib/Transforms/Scalar/Reassociate.cpp"],
        "entries": ["ReassociatePass::run"],
    },
}

TOKEN = re.compile(
    r"""
 (?P<ws>\s+)
|(?P<comment>//[^\n]*|/\*.*?\*/)
|(?P<str>[uUL]?R"(?P<delim>[^(]*)\(.*?\)(?P=delim)"|[uUL8]*"(?:\\.|[^"\\\n])*")
|(?P<chr>[uUL8]*'(?:\\.|[^'\\\n])*')
|(?P<pp>\#[^\n]*(?:\\\n[^\n]*)*)
|(?P<id>[A-Za-z_][A-Za-z0-9_]*)
|(?P<num>\.?[0-9](?:[0-9A-Za-z_.']|[eEpP][+-])*)
|(?P<op>::|->\*?|\.\.\.|<<=|>>=|<=>|&&|\|\||==|!=|<=|>=|\+\+|--|\+=|-=|\*=|/=|%=|&=|\|=|\^=|\.\*|[{}()\[\];,<>?:=+\-*/%&|^!~.@])
""",
    re.X | re.S,
)


@dataclass
class Tok:
    kind: str
    text: str
    line: int


def lex(text: str) -> tuple[list[Tok], list[Tok]]:
    """Code tokens and comments, each with its line. Preprocessor lines are dropped, their code kept."""
    code: list[Tok] = []
    comments: list[Tok] = []
    pos, line = 0, 1
    for m in TOKEN.finditer(text):
        if m.start() != pos:
            raise ValueError(f"can't read the C++ at line {line}: {text[pos : pos + 40]!r}")
        kind, value = m.lastgroup or "", m.group()
        if kind == "comment":
            comments.append(Tok(kind, value, line))
        elif kind not in ("ws", "pp", "delim"):
            code.append(Tok("str" if kind == "chr" else kind, value, line))
        line += value.count("\n")
        pos = m.end()
    if pos != len(text):
        raise ValueError(f"can't read the C++ at line {line}")
    return code, comments


OPEN = {"(": ")", "[": "]", "{": "}"}


def match_close(toks: list[Tok], i: int) -> int:
    """The index of the bracket closing the one at `i`."""
    want = OPEN[toks[i].text]
    depth = 0
    for j in range(i, len(toks)):
        t = toks[j].text
        if t in OPEN:
            depth += 1
        elif t in (")", "]", "}"):
            depth -= 1
            if depth == 0:
                if t != want:
                    raise ValueError(f"unbalanced {toks[i].text!r} at line {toks[i].line}")
                return j
    raise ValueError(f"unclosed {toks[i].text!r} at line {toks[i].line}")


def match_open(toks: list[Tok], j: int) -> int:
    depth = 0
    for i in range(j, -1, -1):
        t = toks[i].text
        if t in (")", "]", "}"):
            depth += 1
        elif t in OPEN:
            depth -= 1
            if depth == 0:
                return i
    raise ValueError(f"unopened {toks[j].text!r} at line {toks[j].line}")


# --- Functions ----------------------------------------------------------------------------------------------

POINTER_RESULT = re.compile(
    r"\b(Value|Instruction|Constant|[A-Za-z]*Inst|[A-Za-z]*Operator|[A-Za-z]*Intrinsic)\s*\*$"
)
QUALIFIERS = ("const", "override", "noexcept", "final", "mutable")
NOT_FUNCTIONS = {"if", "for", "while", "switch", "catch", "return", "sizeof", "alignof", "decltype"}


@dataclass
class Function:
    name: str  # unqualified
    qualified: str
    result: str  # 'pointer', 'bool', 'void' or 'other'
    exported: bool
    file: str
    line: int
    body: tuple[int, int]  # indices of '{' and '}'
    toks: list[Tok]
    parent: Function | None = None
    lambdas: dict[str, Function] = field(default_factory=dict)


def result_kind(ret: str) -> str:
    ret = re.sub(
        r"\[\[[^\]]*\]\]|\b(static|inline|constexpr|LLVM_ABI|const|virtual|template\s*<[^>]*>)\b", " ", ret
    )
    ret = " ".join(ret.replace(" *", "*").replace("*", " *").split())
    inner = re.fullmatch(r"std :: optional < (.*) >", ret)
    if inner:
        ret = inner.group(1)
    if POINTER_RESULT.search(ret.replace(" *", "*").replace("*", " *")):
        return "pointer"
    if ret.endswith("bool"):
        return "bool"
    if ret.endswith("void"):
        return "void"
    return "other"


def find_functions(toks: list[Tok], rel: str) -> list[Function]:
    """Every function body outside another function body, with what it returns."""
    out: list[Function] = []
    i = 0
    while i < len(toks):
        if toks[i].text != "{":
            i += 1
            continue
        j = i - 1
        while j >= 0 and toks[j].text in QUALIFIERS:
            j -= 1
        # A constructor's initializer list: `Ctor(...) : A(a), B(b) {`.
        if j >= 0 and toks[j].text == ")":
            p = match_open(toks, j)
            name_end = p - 1
            k = name_end
            while k - 2 >= 0 and toks[k - 1].text == "::":
                k -= 2
            name = toks[name_end].text if name_end >= 0 else ""
            if (
                toks[name_end].kind == "id"
                and name not in NOT_FUNCTIONS
                and not (k > 0 and toks[k - 1].text in (".", "->"))
            ):
                start = k - 1
                while (start >= 0 and toks[start].text not in (";", "}", "{", ")")) or (
                    start >= 0 and toks[start].text == ")" and toks[start - 1].text != "]"
                ):
                    if toks[start].text == ")":
                        start = match_open(toks, start)
                    if (
                        toks[start].text == ":"
                        and start > 0
                        and toks[start - 1].text in ("public", "private", "protected")
                    ):
                        break
                    start -= 1
                ret_toks = toks[start + 1 : k]
                ret = " ".join(t.text for t in ret_toks)
                end = match_close(toks, i)
                qualified = "".join(t.text for t in toks[k : name_end + 1])
                fn = Function(
                    name=name,
                    qualified=qualified,
                    result=result_kind(ret),
                    exported=qualified.startswith("llvm::")
                    or ("static" not in ret.split() and "::" in qualified),
                    file=rel,
                    line=toks[name_end].line,
                    body=(i, end),
                    toks=toks,
                )
                find_lambdas(fn)
                out.append(fn)
                i = end + 1
                continue
        i += 1
    return out


def find_lambdas(fn: Function) -> None:
    """The lambdas in a function, by the variable each is stored in, or by line if it isn't stored."""
    toks = fn.toks
    a, b = fn.body
    i = a + 1
    while i < b:
        t = toks[i]
        prev = toks[i - 1]
        if (
            t.text == "["
            and toks[i + 1].text != "["
            and prev.text != "["
            and (prev.kind == "op" and prev.text not in (")", "]", ">"))
        ) or (t.text == "[" and prev.text == "return"):
            close = match_close(toks, i)
            k = close + 1
            if toks[k].text == "(":
                k = match_close(toks, k) + 1
            while toks[k].text in QUALIFIERS:
                k += 1
            ret = ""
            if toks[k].text == "->":
                r = k + 1
                while toks[r].text != "{":
                    r += 1
                ret = " ".join(x.text for x in toks[k + 1 : r])
                k = r
            if toks[k].text == "{":
                end = match_close(toks, k)
                name = f"lambda@L{t.line}"
                if prev.text == "=" and toks[i - 2].kind == "id":
                    name = toks[i - 2].text
                lam = Function(
                    name=name,
                    qualified=f"{fn.qualified}::{name}",
                    result=result_kind(ret) if ret else "inferred",
                    exported=False,
                    file=fn.file,
                    line=t.line,
                    body=(k, end),
                    toks=toks,
                    parent=fn,
                )
                if lam.result == "inferred":
                    lam.result = infer_result(lam)
                fn.lambdas[name] = lam
                find_lambdas(lam)
                fn.lambdas.update({n: x for n, x in lam.lambdas.items() if n not in fn.lambdas})
                i = end + 1
                continue
        i += 1


def infer_result(lam: Function) -> str:
    rets = [" ".join(t.text for t in s.expr) for s in returns_of(lam)]
    if rets and all(r in ("true", "false") for r in rets):
        return "bool"
    if not rets or all(r == "" for r in rets):
        return "void"
    return "pointer"


# --- Statements ---------------------------------------------------------------------------------------------


@dataclass
class Stmt:
    kind: str  # block, if, loop, switch, label, return, simple
    start: int
    end: int  # one past the last token
    cond: tuple[int, int] | None = None  # the parenthesized header, without the parentheses
    children: list[Stmt] = field(
        default_factory=list
    )  # block: statements; if: [then, else?]; loop/switch: [body]
    expr: list[Tok] = field(default_factory=list)  # return: its expression


def lambda_ranges(fn: Function) -> list[tuple[int, int]]:
    return [lam.body for lam in fn.lambdas.values() if lam.parent is fn]


def parse_block(toks: list[Tok], a: int, b: int, skip: list[tuple[int, int]]) -> list[Stmt]:
    """The statements between `a` and `b`, exclusive."""
    out = []
    i = a
    while i < b:
        s = parse_stmt(toks, i, b, skip)
        out.append(s)
        i = s.end
    return out


def skip_expr(toks: list[Tok], i: int, b: int, stop: tuple[str, ...]) -> int:
    """The index of the first token in `stop` at depth 0, from `i`."""
    while i < b:
        t = toks[i].text
        if t in OPEN:
            i = match_close(toks, i) + 1
            continue
        if t in stop:
            return i
        i += 1
    return b


def parse_stmt(toks: list[Tok], i: int, b: int, skip: list[tuple[int, int]]) -> Stmt:
    t = toks[i].text
    if t == "{":
        end = match_close(toks, i)
        return Stmt("block", i, end + 1, children=parse_block(toks, i + 1, end, skip))
    if t == ";":
        return Stmt("simple", i, i + 1)
    if t == "if":
        k = i + 1
        if toks[k].text == "constexpr":
            k += 1
        close = match_close(toks, k)
        then = parse_stmt(toks, close + 1, b, skip)
        kids = [then]
        end = then.end
        if end < b and toks[end].text == "else":
            other = parse_stmt(toks, end + 1, b, skip)
            kids.append(other)
            end = other.end
        return Stmt("if", i, end, cond=(k + 1, close), children=kids)
    if t in ("for", "while", "switch"):
        close = match_close(toks, i + 1)
        body = parse_stmt(toks, close + 1, b, skip)
        return Stmt("switch" if t == "switch" else "loop", i, body.end, cond=(i + 2, close), children=[body])
    if t == "do":
        body = parse_stmt(toks, i + 1, b, skip)
        k = body.end  # while
        close = match_close(toks, k + 1)
        return Stmt("loop", i, close + 2, cond=(k + 2, close), children=[body])
    if t in ("case", "default"):
        k = i
        while toks[k].text != ":" or toks[k + 1].text == ":" or toks[k - 1].text == ":":
            if toks[k].text == ":" and toks[k + 1].text == ":":
                k += 2
                continue
            k += 1
        return Stmt("label", i, k + 1, cond=(i, k))
    if (
        toks[i].kind == "id"
        and toks[i + 1].text == ":"
        and toks[i + 2].text != ":"
        and t not in ("public", "private", "protected")
    ):
        return Stmt("label", i, i + 2, cond=(i, i + 1))
    if t == "return":
        end = skip_expr(toks, i + 1, b, (";",))
        return Stmt("return", i, end + 1, expr=toks[i + 1 : end])
    end = skip_expr(toks, i, b, (";",))
    return Stmt("simple", i, end + 1)


def body_of(fn: Function) -> list[Stmt]:
    a, b = fn.body
    return parse_block(fn.toks, a + 1, b, lambda_ranges(fn))


def walk(stmts: list[Stmt], path: tuple[Stmt, ...] = ()):
    """Each statement with the statements enclosing it, outermost first."""
    for s in stmts:
        yield s, path
        for c in s.children:
            yield from walk([c], (*path, s))


def returns_of(fn: Function) -> list[Stmt]:
    inner = lambda_ranges(fn)
    return [
        s for s, _ in walk(body_of(fn)) if s.kind == "return" and not any(x <= s.start <= y for x, y in inner)
    ]


# --- Forwards and sites -------------------------------------------------------------------------------------

NULL_RESULTS = {"nullptr", "false", "", "{ }", "std :: nullopt", "nullopt", "NULL", "None"}
CAST = {
    "cast",
    "dyn_cast",
    "cast_or_null",
    "dyn_cast_or_null",
    "static_cast",
    "cast_if_present",
    "dyn_cast_if_present",
}
# Calls that install a value as the replacement: the replacement is the argument at this index.
INSTALL = {"replaceInstUsesWith": 1, "replaceAllUsesWith": 0}
FLAG = re.compile(r"^(Changed|MadeChange|MadeIRChange|Modified|Changes|MadeChanges)$")
# Calls that build IR or change it in place. A function that declines and makes none of these calls, and isn't
# reached by forwarding, only finds values: a helper, not a fold.
CHANGES = re.compile(
    r"^(Create[A-Z0-9][A-Za-z0-9]*|replaceInstUsesWith|replaceOperand|replaceUse|setOperand|replaceAllUsesWith|"
    r"replaceUsesWithIf|replaceUsesOfWith|eraseInstFromFunction|eraseFromParent|removeFromParent|insertBefore|"
    r"insertAfter|insertInto|moveBefore|moveAfter|swapOperands|setPredicate|setHasNoSignedWrap|"
    r"setHasNoUnsignedWrap|setIsExact|setIsDisjoint|setNonNeg|setSameSign|dropPoisonGeneratingFlags|"
    r"dropPoisonGeneratingAnnotations|dropUBImplyingAttrsAndMetadata|copyIRFlags|andIRFlags|setCondition|"
    r"setArgOperand|setCalledFunction|setCalledOperand|InsertNewInstWith|InsertNewInstBefore|setFastMathFlags|"
    r"copyFastMathFlags|setDebugLoc|setIncomingValue|addIncoming|removeIncomingValue|setMetadata|"
    r"setAlignment|setVolatile|setOrdering|setSyncScopeID|setCannotMerge|setTailCall|addParamAttr|"
    r"removeParamAttr|addRetAttr|setDoesNotThrow|setHasNoNaNs|setHasNoInfs|setHasNoSignedZeros|"
    r"setHasAllowReassoc|setNoWrapFlags|setIsInBounds|setNoWrap)$"
)
# Calls that change IR that's already there. One with no return or flag after it in its block is a site of its
# own.
MUTATES = re.compile(
    r"^(replaceOperand|replaceUse|setOperand|replaceAllUsesWith|replaceUsesWithIf|replaceUsesOfWith|"
    r"replaceInstUsesWith|swapOperands|setPredicate|setHasNoSignedWrap|setHasNoUnsignedWrap|setIsExact|"
    r"setIsDisjoint|setNonNeg|setSameSign|dropPoisonGeneratingFlags|dropPoisonGeneratingAnnotations|"
    r"dropUBImplyingAttrsAndMetadata|copyIRFlags|andIRFlags|setCondition|setArgOperand|setCalledFunction|"
    r"setCalledOperand|setIncomingValue|addIncoming|removeIncomingValue|eraseInstFromFunction|eraseFromParent|"
    r"removeFromParent|moveBefore|moveAfter|insertBefore|insertAfter|setFastMathFlags|copyFastMathFlags|"
    r"setHasNoNaNs|setHasNoInfs|setHasNoSignedZeros|setHasAllowReassoc|setNoWrapFlags|setIsInBounds|"
    r"setVolatile|setOrdering|setAlignment|setTailCall|addParamAttr|removeParamAttr|addRetAttr|"
    r"setDoesNotThrow|setCannotMerge|setSyncScopeID|setMetadata)$"
)
SELF = re.compile(r"^(& [A-Za-z_][A-Za-z0-9_]*|true)$")


def strip(expr: list[Tok]) -> list[Tok]:
    """`expr` without enclosing parentheses or casts."""
    while True:
        if len(expr) >= 2 and expr[0].text == "(" and match_close(expr, 0) == len(expr) - 1:
            expr = expr[1:-1]
            continue
        if expr and expr[0].text in CAST and len(expr) > 2 and expr[1].text == "<":
            k = 1
            depth = 0
            while k < len(expr):
                depth += {"<": 1, ">": -1}.get(expr[k].text, 0)
                if depth == 0:
                    break
                k += 1
            if k + 1 < len(expr) and expr[k + 1].text == "(" and match_close(expr, k + 1) == len(expr) - 1:
                expr = expr[k + 2 : -1]
                continue
        return expr


def ternary(expr: list[Tok]) -> tuple[list[Tok], list[Tok], list[Tok]] | None:
    """`(cond, then, else)` if `expr` is `cond ? then : else` at depth 0."""
    q = skip_expr(expr, 0, len(expr), ("?",))
    if q >= len(expr):
        return None
    depth = 0
    k = q + 1
    while k < len(expr):
        t = expr[k].text
        if t in OPEN:
            k = match_close(expr, k) + 1
            continue
        if t == "?":
            depth += 1
        elif t == ":" and not (k + 1 < len(expr) and expr[k + 1].text == ":") and expr[k - 1].text != ":":
            if depth == 0:
                return expr[:q], expr[q + 1 : k], expr[k + 1 :]
            depth -= 1
        k += 1
    return None


def split_top(expr: list[Tok], op: str) -> list[list[Tok]]:
    """`expr` split at `op` where it's at depth 0."""
    parts: list[list[Tok]] = [[]]
    i = 0
    while i < len(expr):
        t = expr[i]
        if t.text in OPEN:
            c = match_close(expr, i)
            parts[-1].extend(expr[i : c + 1])
            i = c + 1
            continue
        if t.text == op:
            parts.append([])
        else:
            parts[-1].append(t)
        i += 1
    return parts


@dataclass(frozen=True)
class Call:
    name: str
    qual: str  # '', '.', '->' or '::'
    owner: str  # what's before '::'


def call_of(expr: list[Tok]) -> tuple[Call, list[list[Tok]]] | None:
    """The call `expr` is, such as `IC.foo(a, b)`, `X::foo<T>(a)` or `::foo(a)`, with its arguments."""
    expr = strip(expr)
    if not expr or expr[-1].text != ")":
        return None
    p = match_open(expr, len(expr) - 1)
    k = p - 1
    if k >= 0 and expr[k].text == ">":  # template arguments
        depth = 0
        while k >= 0:
            depth += {">": 1, "<": -1}.get(expr[k].text, 0)
            if depth == 0:
                break
            k -= 1
        k -= 1
    if k < 0 or expr[k].kind != "id":
        return None
    q = k
    while q >= 2 and expr[q - 1].text in (".", "->", "::") and expr[q - 2].kind == "id":
        q -= 2
    if q == 1 and expr[0].text == "::":
        q = 0
    if q != 0:
        return None
    args: list[list[Tok]] = []
    inner = expr[p + 1 : -1]
    i = 0
    cur: list[Tok] = []
    while i < len(inner):
        t = inner[i]
        if t.text in OPEN:
            c = match_close(inner, i)
            cur.extend(inner[i : c + 1])
            i = c + 1
            continue
        if t.text == ",":
            args.append(cur)
            cur = []
        else:
            cur.append(t)
        i += 1
    if cur:
        args.append(cur)
    qual = expr[k - 1].text if k >= 1 and expr[k - 1].text in (".", "->", "::") else ""
    owner = expr[k - 2].text if qual == "::" and k >= 2 else ""
    return Call(expr[k].text, qual, owner), args


def text(toks: list[Tok]) -> str:
    return " ".join(t.text for t in toks)


@dataclass
class Site:
    fn: Function
    kind: str  # 'return' or 'flag'
    stmt: Stmt
    path: tuple[Stmt, ...]


def cond_binding(fn: Function, name: str, path: tuple[Stmt, ...]) -> list[Tok] | None:
    """What an enclosing `if (T *name = ...)` binds `name` to, innermost first, if one does."""
    for st in reversed(path):
        if st.kind != "if" or st.cond is None:
            continue
        cond = fn.toks[st.cond[0] : st.cond[1]]
        eq = skip_expr(cond, 0, len(cond), ("=",))
        if (
            2 <= eq < len(cond)
            and cond[eq - 1].text == name
            and (cond[eq - 2].text in ("*", "&") or cond[eq - 2].kind == "id")
        ):
            return cond[eq + 1 :]
    return None


def all_functions(fns: list[Function]) -> list[Function]:
    out = []
    for f in fns:
        out.append(f)
        out.extend(f.lambdas.values())
    return out


class Scanner:
    def __init__(self, src: Path, passes: dict[str, dict[str, Any]] | None = None) -> None:
        self.src = src
        self.passes = passes or PASSES
        self.files: dict[str, tuple[list[Tok], list[Tok]]] = {}
        self.functions: dict[str, list[Function]] = {}  # by pass, lambdas included
        self.by_name: dict[str, list[Function]] = {}  # top-level functions in every pass, by unqualified name
        for p, spec in self.passes.items():
            files = spec["files"]
            rels = (
                sorted(
                    str(x.relative_to(src))
                    for x in (src / files.rsplit("/", 1)[0]).glob(files.rsplit("/", 1)[1])
                )
                if isinstance(files, str)
                else files
            )
            fns: list[Function] = []
            for rel in rels:
                code, comments = lex((src / rel).read_text())
                self.files[rel] = (code, comments)
                fns.extend(find_functions(code, rel))
            self.functions[p] = all_functions(fns)
            for f in fns:
                self.by_name.setdefault(f.name, []).append(f)
        self.info: dict[int, dict[str, Any]] = {}
        every = [f for fns in self.functions.values() for f in fns]
        self.uncertain: dict[int, set[str]] = {id(f): self.uncertain_names(f) for f in every}
        for f in every:
            self.info[id(f)] = {"declines": self.declines(f), "changes": self.changes(f)}
        # A function that returns what a declining function returns declines too. To a fixpoint.
        grew = True
        while grew:
            grew = False
            for f in every:
                if self.info[id(f)]["declines"] or f.result not in ("pointer", "bool"):
                    continue
                binds = self.bindings(f)
                inner = lambda_ranges(f)
                rets = [
                    (r, path)
                    for r, path in walk(body_of(f))
                    if r.kind == "return" and not any(x <= r.start <= y for x, y in inner)
                ]
                if any(self.classify(f, r.expr, binds, path=path)[1] for r, path in rets):
                    self.info[id(f)]["declines"] = True
                    grew = True

    def declines(self, f: Function) -> bool:
        """Whether `f` can answer that it made no change: a null result, or `false`."""
        if f.result not in ("pointer", "bool"):
            return False
        for s in returns_of(f):
            e = strip(s.expr)
            if text(e) in NULL_RESULTS:
                return True
            # A bool that returns a flag can return false. So can `Flag ? &I : nullptr`.
            if f.result == "bool" and len(e) == 1 and e[0].kind == "id" and e[0].text not in ("true",):
                return True
            tern = ternary(e)
            if tern and (text(strip(tern[1])) in NULL_RESULTS or text(strip(tern[2])) in NULL_RESULTS):
                return True
        return False

    def changes(self, f: Function) -> bool:
        toks = f.toks
        a, b = f.body
        for i in range(a, b):
            t = toks[i]
            if t.kind == "id" and toks[i + 1].text in ("(", "<") and CHANGES.match(t.text):
                return True
            if t.text == "new" and toks[i + 1].kind == "id":
                return True
        return False

    def candidate(self, f: Function) -> bool:
        """A function whose result a caller can forward: it can decline, with a null value or a false flag."""
        return self.info[id(f)]["declines"]

    def resolve(self, call: Call, within: Function) -> list[Function]:
        """The functions in the passes' files a call can reach."""
        if call.qual == "":
            f: Function | None = within
            while f is not None:
                if call.name in f.lambdas:
                    return [f.lambdas[call.name]]
                f = f.parent
        found = self.by_name.get(call.name, [])
        if call.qual in (".", "->"):
            # A method call: a member of a class, never a free function.
            return [g for g in found if "::" in g.qualified and not g.qualified.startswith("llvm::")]
        if call.qual == "::":
            if call.owner in ("", "llvm"):
                return [g for g in found if "::" not in g.qualified or g.qualified.startswith("llvm::")]
            return [g for g in found if g.qualified.endswith(f"{call.owner}::{call.name}")]
        return found

    def bindings(self, fn: Function) -> dict[str, list[list[Tok]]]:
        """For each name, every expression assigned to it in the function, but for a declaration in an `if`'s
        condition, which binds only inside that `if`: `cond_binding` finds those."""
        toks = fn.toks
        a, b = fn.body
        out: dict[str, list[list[Tok]]] = {}
        conds = [s.cond for s, _ in walk(body_of(fn)) if s.kind == "if" and s.cond is not None]
        for i in range(a + 1, b):
            if (
                toks[i].text == "="
                and toks[i - 1].kind == "id"
                and (toks[i - 2].text in ("*", "&") or toks[i - 2].kind == "id")
                and any(x <= i < y for x, y in conds)
            ):
                continue
            if toks[i].text == "=" and toks[i - 1].kind == "id" and toks[i - 2].text not in (".", "->", "::"):
                end = skip_expr(toks, i + 1, b, (";", ",", ")"))
                out.setdefault(toks[i - 1].text, []).append(toks[i + 1 : end])
        return out

    def uncertain_names(self, fn: Function) -> set[str]:
        """Names a matcher binds, such as `X` in `m_Value(X)`: a return of one may hold the site's own value,
        whatever else is assigned to it."""
        toks = fn.toks
        a, b = fn.body
        out: set[str] = set()
        for i in range(a + 1, b):
            t = toks[i]
            if t.text == "(" and toks[i - 1].kind == "id" and toks[i - 1].text.startswith("m_"):
                if toks[i - 1].text.startswith(("m_Specific", "m_Deferred")):
                    continue
                close = match_close(toks, i)
                depth = 0
                for k in range(i + 1, close):
                    depth += {"(": 1, "[": 1, "{": 1, ")": -1, "]": -1, "}": -1}.get(toks[k].text, 0)
                    if (
                        depth == 0
                        and toks[k].kind == "id"
                        and toks[k - 1].text in ("(", ",")
                        and toks[k + 1].text in (")", ",")
                    ):
                        out.add(toks[k].text)
        return out

    def classify(
        self,
        fn: Function,
        expr: list[Tok],
        binds: dict[str, list[list[Tok]]],
        seen: frozenset[str] = frozenset(),
        path: tuple[Stmt, ...] = (),
    ) -> tuple[bool, list[Function]]:
        """Whether returning `expr` makes a change of the function's own, and the folds whose results it
        forwards."""
        expr = strip(expr)
        if text(expr) in NULL_RESULTS:
            return False, []
        tern = ternary(expr)
        if tern:
            s1, e1 = self.classify(fn, tern[1], binds, seen, path)
            s2, e2 = self.classify(fn, tern[2], binds, seen, path)
            return s1 or s2, e1 + e2
        # `fold1(...) || fold2(...)`, in a bool fold: each fold's change is its own.
        parts = split_top(expr, "||")
        if len(parts) > 1 and fn.result == "bool":
            site, edges = False, []
            for part in parts:
                s1, e1 = self.classify(fn, part, binds, seen, path)
                site, edges = site or s1, edges + e1
            return site, edges
        call = call_of(expr)
        if call:
            c, args = call
            if c.name in INSTALL and c.qual in ("", ".", "->") and len(args) > INSTALL[c.name]:
                return self.classify(fn, args[INSTALL[c.name]], binds, seen, path)
            targets = [t for t in self.resolve(c, fn) if self.candidate(t)]
            return (False, targets) if targets else (True, [])
        if len(expr) == 1 and expr[0].kind == "id" and path:
            rhs = cond_binding(fn, expr[0].text, path)
            if rhs is not None:
                return self.classify(fn, rhs, binds, seen | {expr[0].text})
        if len(expr) == 1 and expr[0].kind == "id" and expr[0].text in self.uncertain.get(id(fn), set()):
            # Bound by a matcher: what it holds may be the site's own value. Any fold it may hold is still
            # reached.
            edges = []
            for rhs in binds.get(expr[0].text, []) if expr[0].text not in seen else []:
                edges += self.classify(fn, rhs, binds, seen | {expr[0].text})[1]
            return True, edges
        if len(expr) == 1 and expr[0].kind == "id" and expr[0].text in binds and expr[0].text not in seen:
            # A name assigned only null, or nothing a fold returns, is bound by a matcher: what it holds is
            # the site's.
            site, edges = False, []
            for rhs in binds[expr[0].text]:
                s, e = self.classify(fn, rhs, binds, seen | {expr[0].text})
                site, edges = site or s, edges + e
            return (site or not edges), edges
        return True, []

    def guard_call(self, fn: Function, stmt: Stmt, path: tuple[Stmt, ...]) -> list[Function]:
        """If `stmt` is the whole then-branch of an `if` whose condition is a call to a fold, that fold."""
        parent = path[-1] if path else None
        if parent is not None and parent.kind == "block" and len(parent.children) == 1 and len(path) >= 2:
            parent, stmt = path[-2], parent
        if parent is None or parent.kind != "if" or parent.children[0] is not stmt or parent.cond is None:
            return []
        cond = fn.toks[parent.cond[0] : parent.cond[1]]
        eq = skip_expr(cond, 0, len(cond), ("=",))
        if eq < len(cond):
            cond = cond[eq + 1 :]
        call = call_of(cond)
        if not call:
            return []
        return [t for t in self.resolve(call[0], fn) if self.candidate(t)]

    def installs(
        self, fn: Function, stmt: Stmt, path: tuple[Stmt, ...], binds: dict[str, list[list[Tok]]]
    ) -> list[Function]:
        """If `stmt` is in the block of an `if (T *V = fold(...))` that only installs V, as a driver does,
        that fold. Installing is `replaceAllUsesWith(V)` or `replaceInstUsesWith(I, V)`, and nothing else
        changes."""
        for k in range(len(path) - 1, -1, -1):
            s = path[k]
            if s.kind != "if" or s.cond is None:
                continue
            branch = path[k + 1] if k + 1 < len(path) else stmt
            if s.children[0] is not branch:
                return []
            cond = fn.toks[s.cond[0] : s.cond[1]]
            eq = skip_expr(cond, 0, len(cond), ("=",))
            if eq >= len(cond) or cond[eq - 1].kind != "id":
                return []
            var = cond[eq - 1].text
            call = call_of(cond[eq + 1 :])
            if not call:
                return []
            folds = [t for t in self.resolve(call[0], fn) if self.candidate(t)]
            body = fn.toks[branch.start : branch.end]
            installed = False
            for i, t in enumerate(body):
                if t.kind == "id" and i + 1 < len(body) and body[i + 1].text == "(" and CHANGES.match(t.text):
                    close = match_close(body, i + 1)
                    args = text(body[i + 2 : close])
                    if t.text in INSTALL and (args == var or args.endswith(f", {var}")):
                        installed = True
                        continue
                    return []
            return folds if installed else []
        return []

    def unclaimed_change(self, fn: Function, stmt: Stmt, path: tuple[Stmt, ...]) -> bool:
        """Whether `stmt` changes IR in place, with no site after it in its block to commit it: a return or
        a changed flag that's a site of its own, not a forward. `replaceUse(U, V);` alone in a lambda is one,
        and so is a change to a value a lookup returned before `return` forwards it. Then the statement is the
        site."""
        toks = fn.toks
        inner = lambda_ranges(fn)
        if not any(
            toks[k].kind == "id"
            and MUTATES.match(toks[k].text)
            and toks[k + 1].text == "("
            and not any(x <= k <= y for x, y in inner)
            for k in range(stmt.start, stmt.end - 1)
        ):
            return False
        block = path[-1] if path else None
        if block is not None and block.kind != "block":
            return True
        siblings = block.children if block is not None else body_of(fn)
        binds = self.bindings(fn)
        after = False
        for c in siblings:
            if c.start == stmt.start:
                after = True
                continue
            if not after:
                continue
            for x, sub in walk([c]):
                full = (*path, *sub)
                if x.kind == "return" and fn.result in ("pointer", "bool"):
                    e = text(strip(x.expr))
                    if e in NULL_RESULTS:
                        continue
                    if SELF.match(e):
                        if not (self.guard_call(fn, x, full) or self.installs(fn, x, full, binds)):
                            return False
                        continue
                    if fn.result == "bool" and len(x.expr) == 1 and x.expr[0].kind == "id":
                        return False  # a flag returned: the change it records is this one
                    if self.classify(fn, x.expr, binds, path=full)[0]:
                        return False
                if x.kind == "simple":
                    xs = toks[x.start : x.end - 1]
                    if (
                        len(xs) >= 3
                        and FLAG.match(xs[0].text)
                        and xs[1].text in ("=", "|=")
                        and text(xs[2:]) == "true"
                    ):
                        return False
        return True

    def analyse(self, fn: Function) -> tuple[list[Site], list[Function]]:
        """The sites in `fn`, and the folds it forwards to."""
        sites: list[Site] = []
        edges: list[Function] = []
        binds = self.bindings(fn)
        inner = lambda_ranges(fn)
        toks = fn.toks
        for s, path in walk(body_of(fn)):
            if any(x <= s.start <= y for x, y in inner):
                continue
            if s.kind == "return" and fn.result in ("pointer", "bool"):
                e = text(strip(s.expr))
                if e in NULL_RESULTS:
                    continue
                if SELF.match(e):
                    g = self.guard_call(fn, s, path) or self.installs(fn, s, path, binds)
                    if g:
                        edges.extend(g)
                    else:
                        sites.append(Site(fn, "return", s, path))
                    continue
                if fn.result == "bool" and len(s.expr) == 1 and s.expr[0].kind == "id":
                    continue  # a flag, set where the change is made
                tern = ternary(strip(s.expr))
                if tern and len(strip(tern[0])) == 1 and FLAG.match(strip(tern[0])[0].text):
                    continue  # `Changed ? &I : nullptr`: the sites are where the flag is set
                site, e2 = self.classify(fn, s.expr, binds, path=path)
                edges.extend(e2)
                if site:
                    sites.append(Site(fn, "return", s, path))
            elif s.kind == "simple":
                st = toks[s.start : s.end - 1]
                if (
                    len(st) >= 3
                    and st[0].kind == "id"
                    and FLAG.match(st[0].text)
                    and st[1].text in ("=", "|=")
                ):
                    rhs = st[2:]
                    if text(rhs) == "true":
                        g = self.guard_call(fn, s, path) or self.installs(fn, s, path, binds)
                        if g:
                            edges.extend(g)
                        else:
                            sites.append(Site(fn, "flag", s, path))
                    else:
                        call = call_of(rhs)
                        if call:
                            edges.extend(t for t in self.resolve(call[0], fn) if self.candidate(t))
                    continue
                # Installing a fold's result, `I->replaceAllUsesWith(V)`, is a forward, not a change of its
                # own.
                installed = call_of(st)
                forwards = False
                if (
                    installed
                    and installed[0].name in INSTALL
                    and len(installed[1]) > INSTALL[installed[0].name]
                ):
                    own, folds = self.classify(fn, installed[1][INSTALL[installed[0].name]], binds, path=path)
                    forwards = not own and bool(folds)
                if not forwards and self.unclaimed_change(fn, s, path):
                    sites.append(Site(fn, "change", s, path))
                # A call made for what it changes, `foo(I);`, or that installs a fold's result,
                # `I->replaceAllUsesWith(V);`.
                if len(st) > 3 and st[0].text == "(" and st[1].text == "void":
                    st = st[3:]
                call = call_of(st)
                if call:
                    c, args = call
                    if c.name in INSTALL and len(args) > INSTALL[c.name]:
                        edges.extend(self.classify(fn, args[INSTALL[c.name]], binds, path=path)[1])
                    else:
                        edges.extend(t for t in self.resolve(c, fn) if t.result in ("void", "bool"))
            elif s.kind == "if" and s.cond is not None:
                # `if (foo(I))` where the branch isn't only a return: the change is foo's.
                cond = toks[s.cond[0] : s.cond[1]]
                call = call_of(cond)
                if call:
                    edges.extend(
                        t
                        for t in self.resolve(call[0], fn)
                        if t.result == "bool" and self.info[id(t)]["changes"]
                    )
        return sites, edges

    def entries(self, p: str) -> list[Function]:
        out = []
        for f in self.functions[p]:
            if f.parent is not None:
                continue
            for e in self.passes[p]["entries"]:
                if (
                    (
                        e == "@visit"
                        and f.name.startswith("visit")
                        and f.qualified.startswith("InstCombinerImpl::")
                    )
                    or (e == "@exported" and f.exported and f.name.startswith("simplify"))
                    or ("::" in e and f.qualified == e)
                    or ("::" not in e and f.name == e)
                ):
                    out.append(f)
        return out

    def reach(self) -> tuple[dict[int, Function], dict[int, list[Site]], dict[int, str]]:
        """The folds, the sites in each, and why each is a fold: reached from an entry by forwarding, or a
        function that declines and builds or changes IR."""
        seen: dict[int, Function] = {}
        why: dict[int, str] = {}
        sites: dict[int, list[Site]] = {}
        todo = [(f, "entry") for p in self.passes for f in self.entries(p)]
        todo += [
            (f, "builds")
            for p in self.passes
            for f in self.functions[p]
            if self.info[id(f)]["declines"] and self.info[id(f)]["changes"]
        ]
        while todo:
            f, reason = todo.pop(0)
            if id(f) in seen:
                continue
            seen[id(f)] = f
            why[id(f)] = reason
            s, edges = self.analyse(f)
            sites[id(f)] = s
            todo.extend((e, "forwarded") for e in edges if id(e) not in seen)
        return seen, sites, why


# --- What a site needs --------------------------------------------------------------------------------------

# Intrinsics IRLean models as integer operations, in src/Emitter.cpp and IRLean/Int.lean.
INT_INTRINSICS = {
    "abs", "umin", "umax", "smin", "smax", "ctpop", "ctlz", "cttz", "bswap", "bitreverse", "fshl", "fshr",
    "uadd_sat", "usub_sat", "sadd_sat", "ssub_sat", "uadd_with_overflow", "sadd_with_overflow",
    "usub_with_overflow", "ssub_with_overflow", "umul_with_overflow", "smul_with_overflow", "ucmp", "scmp",
    "assume", "expect", "vector_reduce_add", "vector_reduce_mul", "vector_reduce_and", "vector_reduce_or",
    "vector_reduce_xor", "vector_reduce_umin", "vector_reduce_umax", "vector_reduce_smin",
    "vector_reduce_smax",
}  # fmt: skip
FP_INTRINSICS = re.compile(
    r"^(fabs|copysign|minnum|maxnum|minimum|maximum|minimumnum|maximumnum|fma|fmuladd|sqrt|sin|cos|tan|asin|acos|"
    r"atan|atan2|sinh|cosh|tanh|exp|exp2|exp10|log|log2|log10|pow|powi|floor|ceil|trunc|rint|nearbyint|round|"
    r"roundeven|lrint|llrint|lround|llround|ldexp|frexp|is_fpclass|canonicalize|arithmetic_fence|fptosi_sat|"
    r"fptoui_sat|fptrunc_round|experimental_constrained_.*|vector_reduce_f.*|convert_.*fp.*|modf|sincos.*)$"
)
MEM_INTRINSICS = re.compile(
    r"^(memcpy|memcpy_inline|memmove|memset|memset_inline|memset_pattern|lifetime_.*|invariant_.*|masked_.*|ptrmask|"
    r"threadlocal_address|objectsize|launder_invariant_group|strip_invariant_group|prefetch|vp_load|vp_store|"
    r"vp_gather|vp_scatter|experimental_vp_strided_.*|load_relative|stacksave|stackrestore|is_constant|"
    r"experimental_gc_.*|preserve_.*)$"
)
FP_IDS = re.compile(
    r"^(FAdd|FSub|FMul|FDiv|FRem|FNeg|FCmp|FCmpInst|FPExt|FPTrunc|FPToSI|FPToUI|SIToFP|UIToFP|FPExtInst|FPTruncInst|"
    r"SIToFPInst|UIToFPInst|FPToSIInst|FPToUIInst|ConstantFP|APFloat|FastMathFlags|FPMathOperator|isFPOrFPVectorTy|"
    r"isFloatingPointTy|getFltSemantics|fltSemantics|KnownFPClass|FPClassTest|computeKnownFPClass|"
    r"cannotBeNegativeZero|cannotBeOrderedLessThanZero|isKnownNeverNaN|isKnownNeverInfinity|isKnownNeverNegZero|"
    r"CreateFAdd|CreateFSub|CreateFMul|CreateFDiv|CreateFRem|CreateFNeg|CreateFCmp|CreateFPExt|CreateFPTrunc|"
    r"CreateFAddFMF|CreateFSubFMF|CreateFMulFMF|CreateFDivFMF|CreateFNegFMF|CreateFCmpFMF|CreateFPCast|"
    r"CreateSIToFP|CreateUIToFP|CreateFPToSI|CreateFPToUI|getFastMathFlags|hasNoNaNs|hasNoInfs|hasNoSignedZeros|"
    r"hasAllowReassoc|hasAllowReciprocal|hasApproxFunc|hasAllowContract|isFast|copyFastMathFlags|"
    r"FCMP_[A-Z]+|fcmp|isFPPredicate|getFPMantissaWidth|isIEEE|BinaryOpIntrinsic_FP|m_SpecificFP|"
    r"isKnownNeverNaNOrInf|getFPValue|LibFunc_.*f|Float|Double|isHalfTy|isFloatTy|isDoubleTy)$"
)
FP_MATCHERS = re.compile(
    r"^m_(F[A-Z][A-Za-z]*|AnyZeroFP|PosZeroFP|NegZeroFP|NaN|NonNaN|Inf|NonInf|Finite|FiniteNonZero|NonZeroFP|"
    r"SIToFP|UIToFP|FPToSI|FPToUI|ConstantFP|SpecificFP|CombineOr_FP|OrdOrUnordFMin|OrdOrUnordFMax|"
    r"OrdFMin|OrdFMax|UnordFMin|UnordFMax|CopySign)$"
)
MEM_IDS = re.compile(
    r"^(LoadInst|StoreInst|AllocaInst|GetElementPtrInst|GEPOperator|AtomicRMWInst|AtomicCmpXchgInst|FenceInst|"
    r"MemIntrinsic|MemTransferInst|MemSetInst|MemCpyInst|MemMoveInst|AnyMemIntrinsic|AnyMemTransferInst|"
    r"AnyMemSetInst|MemCpyInlineInst|isPointerTy|isPtrOrPtrVectorTy|PointerType|PtrToIntInst|IntToPtrInst|"
    r"PtrToAddrInst|AddrSpaceCastInst|getPointerOperand|getPointerAddressSpace|getUnderlyingObject|"
    r"stripPointerCasts|stripPointerCastsAndAliases|stripInBoundsOffsets|stripAndAccumulateConstantOffsets|"
    r"stripAndComputeConstantOffsets|GlobalVariable|GlobalValue|GlobalAlias|AAResults|AliasAnalysis|"
    r"isDereferenceablePointer|isDereferenceableAndAlignedPointer|isSafeToLoadUnconditionally|"
    r"computePointerICmp|computePointerDifference|getLoadStorePointerOperand|getLoadStoreType|isNoAliasCall|"
    r"PtrToInt|IntToPtr|AddrSpaceCast|GetElementPtr|Load|Store|Alloca|CreateLoad|CreateStore|CreateAlignedLoad|"
    r"CreateAlignedStore|CreateGEP|CreateInBoundsGEP|CreatePtrAdd|CreateInBoundsPtrAdd|CreatePtrToInt|"
    r"CreateIntToPtr|CreatePointerCast|CreateAddrSpaceCast|CreateMemCpy|CreateMemSet|CreateMemMove|"
    r"getGEPIndicesForOffset|EmitGEPOffset|isAllocSiteRemovable|isAllocLikeFn|isFreeCall|getAllocAlignment|"
    r"isRemovableAlloc|isNonEscapingLocalObject|PointerMayBeCaptured|isIdentifiedObject|DataLayout_ptr|"
    r"isKnownNonNull|getPointerElementType|ConstantPointerNull|isa_GEP|PHINode_ptr|SimplifyQuery_ptr|"
    r"isOnlyCopiedFromConstantMemory|canReplacePointersIfEqual|canReplacePointersInUseIfEqual)$"
)
MEM_MATCHERS = re.compile(
    r"^m_(PtrToInt|PtrToIntSameSize|IntToPtr|PtrToAddr|GEP|PtrAdd|Load|Store|AddrSpaceCast)$"
)
CALL_IDS = re.compile(
    r"^(CallInst|CallBase|InvokeInst|CallBrInst|IntrinsicInst|getIntrinsicID|getCalledFunction|getCalledOperand|"
    r"LibFunc|TargetLibraryInfo|TLI|isLibFuncEmittable|emitUnaryFloatFnCall|CreateCall|CreateIntrinsic|"
    r"CreateUnaryIntrinsic|CreateBinaryIntrinsic|getOrInsertDeclaration|Function|isa_Call|"
    r"MinMaxIntrinsic|SaturatingInst|WithOverflowInst|BinaryOpIntrinsic|CmpIntrinsic|"
    r"m_Intrinsic|m_Call|isInstructionTriviallyDead|wouldInstructionBeTriviallyDead)$"
)
VECTOR_IDS = re.compile(
    r"^(ShuffleVectorInst|ExtractElementInst|InsertElementInst|VectorType|FixedVectorType|ScalableVectorType|"
    r"isVectorTy|getNumElements|getElementCount|m_Shuffle|m_ExtractElt|m_InsertElt|m_ZeroMask|m_SplatOrPoisonMask|"
    r"ShuffleMask|getShuffleMask|CreateShuffleVector|CreateExtractElement|CreateInsertElement|CreateVectorSplat|"
    r"getSplatValue|isSplat|ConstantVector|ConstantDataVector|isScalableTy|ExtractValueInst|InsertValueInst|"
    r"m_ExtractValue|m_InsertValue)$"
)
CFG_IDS = re.compile(
    r"^(PHINode|BranchInst|SwitchInst|BasicBlock|dominates|isPotentiallyReachable|"
    r"getSinglePredecessor|predecessors|successors|getTerminator|CreatePHI|m_Br|UnreachableInst|ReturnInst|"
    r"foldOpIntoPhi|foldBinopWithPhiOperands|foldPHIArgOpIntoPHI|isGuaranteedToTransferExecutionToSuccessor|"
    r"LoopInfo)$"
)
ANALYSES = re.compile(
    r"^(computeKnownBits|computeKnownBitsFromContext|MaskedValueIsZero|ComputeNumSignBits|ComputeMaxSignificantBits|"
    r"isKnownToBeAPowerOfTwo|isKnownNonZero|isKnownNonNegative|isKnownPositive|isKnownNegative|isKnownNegation|"
    r"isKnownNonEqual|isKnownInversion|haveNoCommonBitsSet|isImpliedCondition|isImpliedByDomCondition|"
    r"willNotOverflowSignedAdd|willNotOverflowUnsignedAdd|willNotOverflowSignedSub|willNotOverflowUnsignedSub|"
    r"willNotOverflowSignedMul|willNotOverflowUnsignedMul|willNotOverflow|computeOverflowForSignedAdd|"
    r"computeOverflowForUnsignedAdd|computeOverflowForSignedSub|computeOverflowForUnsignedSub|"
    r"computeOverflowForSignedMul|computeOverflowForUnsignedMul|computeOverflow|computeConstantRange|"
    r"computeConstantRangeIncludingKnownBits|isGuaranteedNotToBePoison|isGuaranteedNotToBeUndef|"
    r"isGuaranteedNotToBeUndefOrPoison|impliesPoison|canCreatePoison|canCreateUndefOrPoison|"
    r"programUndefinedIfPoison|matchSelectPattern|getInverseMinMaxIntrinsic|SimplifyDemandedBits|"
    r"SimplifyDemandedInstructionBits|SimplifyDemandedUseBits|SimplifyDemandedVectorElts|"
    r"SimplifyMultipleUseDemandedBits|getKnownSign|getKnownSignOrZero|LazyValueInfo|isSafeToSpeculativelyExecute|"
    r"isSafeToSpeculativelyExecuteWithOpcode|canEvaluateTruncated|canEvaluateZExtd|canEvaluateSExtd|"
    r"canEvaluateShifted|cannotBeNegativeZero|isKnownNeverNaN|computeKnownFPClass|KnownBits|ConstantRange|"
    r"isCheckForZeroAndMulWithOverflow|getUnderlyingObject|isKnownExactCastIntToFP|DomConditionCache|"
    r"getRange|computeKnownBitsFromAssume)$"
)
UNDEF_IDS = re.compile(
    r"^(isUndefValue|m_Undef|UndefValue|m_UndefValue|containsUndefElement|isUndef|CanUseUndef|getWithoutUndef)$"
)


def tokens_of(fn: Function, site: Site) -> list[Tok]:
    """What a site's path reads: the function's parameters, the headers of the statements around it, the plain
    statements before it in each block, and the site itself."""
    toks = fn.toks
    out: list[Tok] = []
    # Parameters, for a visit method's instruction type.
    a = fn.body[0]
    j = a - 1
    while j >= 0 and toks[j].text in QUALIFIERS:
        j -= 1
    if toks[j].text == ")":
        out.extend(toks[match_open(toks, j) : j + 1])
    enclosing = (*site.path, site.stmt)
    for k, s in enumerate(enclosing):
        if s.cond is not None:
            out.extend(toks[s.cond[0] : s.cond[1]])
        if s.kind in ("block", "switch") or (s.kind in ("if", "loop") and k + 1 < len(enclosing)):
            nxt = enclosing[k + 1] if k + 1 < len(enclosing) else None
            kids = s.children if s.kind == "block" else []
            if k > 0 and enclosing[k - 1].kind == "switch":
                # A switch's body: only the statements of the case the site is in.
                before = [c for c in kids if nxt is None or c.start < nxt.start]
                labels = [n for n, c in enumerate(before) if c.kind == "label"]
                kids = before[labels[-1] + 1 :] if labels else before
            for c in kids:
                if nxt is not None and c.start >= nxt.start:
                    break
                if c.kind == "simple":
                    out.extend(toks[c.start : c.end])
            if s.kind == "switch" and nxt is not None:
                # The case labels the site is under: the run of labels last before it in the switch's body.
                labels: list[Stmt] = []
                last_was_label = False
                for c in s.children[0].children if s.children and s.children[0].kind == "block" else []:
                    if c.start > site.stmt.start:
                        break
                    if c.kind == "label":
                        labels = [*labels, c] if last_was_label else [c]
                        last_was_label = True
                    else:
                        last_was_label = False
                for c in labels:
                    out.extend(toks[c.cond[0] : c.cond[1]] if c.cond else [])
    out.extend(toks[site.stmt.start : site.stmt.end])
    return out


# Folds of an opcode that's only ever on integers.
INT_ONLY_NAME = re.compile(
    r"^(visit|simplify|fold)?(Add|Sub|Mul|And|Or|Xor|Shl|LShr|AShr|UDiv|SDiv|URem|SRem|ICmp|ZExt|SExt|Trunc)"
    r"(Inst)?$|ICmp"
)
# What on a site's path says its values are integers.
INT_GUARD = re.compile(
    r"^(isIntOrIntVectorTy|isIntegerTy|ConstantInt|APInt|m_APInt[A-Za-z]*|m_ConstantInt|IntegerType|"
    r"getIntegerBitWidth|ICmpInst|m_ICmp|m_c_ICmp|m_SpecificICmp|ICMP_[A-Z]+|m_(c_)?(Add|Sub|Mul|And|Or|Xor)|"
    r"m_(NSW|NUW)[A-Za-z]+|m_(Shl|LShr|AShr|UDiv|SDiv|URem|SRem|Not|Neg|ZExt|SExt|Trunc|ZExtOrSExt|Power2|"
    r"AllOnes|SignMask|LowBitMask|LogicalAnd|LogicalOr)|getScalarSizeInBits)$"
)
# Files whose folds serve floating point as well as integers throughout, whatever each function mentions.
FP_GENERIC_FILES = {"lib/Transforms/Scalar/Reassociate.cpp"}
INT_OPCODES = {"Add", "Sub", "Mul", "And", "Or", "Xor", "Shl", "LShr", "AShr", "UDiv", "SDiv", "URem", "SRem"}


def root_of(fn: Function) -> Function:
    while fn.parent is not None:
        fn = fn.parent
    return fn


def int_guarded(toks: list[Tok]) -> bool:
    """Whether the path says the site's values are integers: a matcher or type test only integers pass, or an
    integer opcode, `Instruction::Add` and the like."""
    for k, t in enumerate(toks):
        if t.kind == "id" and INT_GUARD.match(t.text):
            return True
        if (
            t.text == "Instruction"
            and k + 2 < len(toks)
            and toks[k + 1].text == "::"
            and toks[k + 2].text in INT_OPCODES
        ):
            return True
    return False


def needs(fn: Function, site: Site) -> dict[str, Any]:
    ids = [t.text for t in tokens_of(fn, site) if t.kind == "id"]
    ids_set = set(ids)
    name = fn.name if fn.parent is None else f"{fn.parent.name}"
    intrinsics: set[str] = set()
    toks = tokens_of(fn, site)
    for k in range(len(toks) - 2):
        if toks[k].text == "Intrinsic" and toks[k + 1].text == "::" and toks[k + 2].kind == "id":
            intrinsics.add(toks[k + 2].text)
    fp = (
        any(FP_IDS.match(x) or FP_MATCHERS.match(x) for x in ids_set)
        or bool(
            re.search(
                r"F(Add|Sub|Mul|Div|Rem|Neg|Cmp|Abs|Sqrt|Trunc|Ext|Pow|Max|Min)|FP|Float|Fabs|FMA|Sqrt|NaN|Minnum|Maxnum|CopySign|Powi|Exp2|Log2|Ldexp|Frexp",
                name,
            )
        )
        or any(FP_INTRINSICS.match(x) for x in intrinsics)
    )
    mem = (
        any(MEM_IDS.match(x) or MEM_MATCHERS.match(x) for x in ids_set)
        or bool(
            re.search(
                r"Load|Store|Alloca|GEP|GetElementPtr|Ptr|Pointer|Mem|Atomic|Fence|Alloc|Global|Lifetime",
                name,
            )
        )
        or any(MEM_INTRINSICS.match(x) for x in intrinsics)
    )
    unmodelled = {
        x
        for x in intrinsics
        if x not in INT_INTRINSICS and not FP_INTRINSICS.match(x) and not MEM_INTRINSICS.match(x)
    }
    call_ids = {x for x in ids_set if CALL_IDS.match(x)}
    calls = bool(unmodelled) or bool(
        re.search(r"Call|Invoke|LibFunc|Intrinsic|StrNCmp|MemChr|Sqrt", name) and not intrinsics
    )
    if call_ids and not (intrinsics and intrinsics <= INT_INTRINSICS):
        calls = True
    # A function that rewrites floating point as well as integers, such as Reassociate's `RewriteExprTree`,
    # rewrites both at a site whose path doesn't say the type is an integer.
    generic = False
    if not fp and not INT_ONLY_NAME.search(fn.name if fn.parent is None else root_of(fn).name):
        root = root_of(fn)
        body = {t.text for t in root.toks[root.body[0] : root.body[1]] if t.kind == "id"}
        # Reassociate's every function serves integer and fast-math floating-point reassociation alike, from
        # `OptimizeInst`, so its sites are generic whatever their own function mentions.
        handles_fp = fn.file in FP_GENERIC_FILES or any(FP_IDS.match(x) or FP_MATCHERS.match(x) for x in body)
        if handles_fp and not int_guarded(toks):
            fp = generic = True
    blocked = [k for k, v in (("fp", fp), ("memory", mem), ("calls", calls)) if v]
    also = [k for k, v in (
        ("generic", generic),
        ("vector", any(VECTOR_IDS.match(x) for x in ids_set)),
        ("cfg", any(CFG_IDS.match(x) for x in ids_set)),
        ("undef", any(UNDEF_IDS.match(x) for x in ids_set)),
    ) if v]  # fmt: skip
    return {
        "needs": blocked or ["int"],
        "also": also,
        "analyses": sorted({x for x in ids_set if ANALYSES.match(x)}),
        "intrinsics": sorted(intrinsics),
    }


# --- The inventory ------------------------------------------------------------------------------------------


def comment_above(comments: list[Tok], fn: Function, site: Site) -> str:
    """The comment closest above the site, or above the statement it's the branch of, inside the function."""
    toks = fn.toks
    anchor = site.stmt
    for s in reversed(site.path):
        if s.kind in ("if",) and (
            s.children[0] is anchor
            or (s.children[0].kind == "block" and anchor in s.children[0].children[:1])
        ):
            anchor = s
        else:
            break
    lo = toks[fn.body[0]].line
    first = toks[anchor.start].line
    site_line = toks[site.stmt.start].line
    best: list[str] = []
    for c in comments:
        if lo <= c.line < site_line and (c.line < first or c.line > first) and c.line >= lo:
            pass
    # The comment block ending right above the anchor statement, or right above the site.
    for target in (site_line, first):
        block: list[str] = []
        want = target - 1
        for c in reversed([c for c in comments if lo <= c.line < target]):
            last = c.line + c.text.count("\n")
            if last == want:
                block.insert(0, c.text)
                want = c.line - 1
            elif last < want:
                break
        if block:
            best = block
            break
    out = " ".join(
        re.sub(r"^\s*(//+|/\*+|\*+/?|\*)\s?", "", ln).strip() for b in best for ln in b.splitlines()
    )
    return " ".join(out.replace("*/", "").split())


def function_label(fn: Function) -> str:
    parts = fn.qualified.split("::")
    parts = [p for p in parts if p not in ("llvm", "InstCombinerImpl", "InstCombiner", "ReassociatePass")]
    return ".".join(parts) if parts else fn.name


def file_label(rel: str) -> str:
    stem = Path(rel).stem
    for prefix in ("InstCombine",):
        if stem.startswith(prefix) and stem != prefix:
            stem = stem[len(prefix) :]
    return stem


def site_id(prefix: str, rel: str, fn: Function, line: int, multi_file: bool) -> str:
    label = function_label(fn)
    root = fn
    while root.parent is not None:
        root = root.parent
    if fn.parent is not None:
        label = function_label(root) + "." + fn.name.replace("@", "_")
    middle = f"{file_label(rel)}." if multi_file else ""
    return f"{prefix}.{middle}{label}.L{line}"


def inventory(src: Path, passes: dict[str, dict[str, Any]] | None = None) -> dict[str, Any]:
    sc = Scanner(src, passes)
    folds, sites, why = sc.reach()
    out: dict[str, Any] = {}
    for p, spec in sc.passes.items():
        multi = isinstance(spec["files"], str) or len(spec["files"]) > 1
        rows = []
        mine = {id(f) for f in sc.functions[p]}
        files = sorted({f.file for f in sc.functions[p]})
        for key, f in folds.items():
            if key not in mine:
                continue
            for s in sites[key]:
                comments = sc.files[f.file][1]
                line = f.toks[s.stmt.start].line
                body = text(f.toks[s.stmt.start : s.stmt.end])
                rows.append(
                    {
                        "id": site_id(spec["prefix"], f.file, f, line, multi and p != "instsimplify"),
                        "file": f"llvm/{f.file}",
                        "line": line,
                        "function": f.qualified,
                        "kind": s.kind,
                        "comment": comment_above(comments, f, s),
                        "code": body if len(body) <= 160 else body[:157] + "...",
                        "hash": hashing.sha256_parts(f.qualified, body)[:16],
                        **needs(f, s),
                    }
                )
        rows.sort(key=lambda r: (r["file"], r["line"], r["code"]))
        # Two sites on one line get a suffix, in order.
        seen: Counter[str] = Counter()
        for r in rows:
            rid = str(r["id"])
            seen[rid] += 1
            if seen[rid] > 1:
                r["id"] = f"{rid}.{seen[rid]}"
        hashes = {f"llvm/{rel}": hashing.sha256_file(src / rel) for rel in files}
        fold_rows = sorted(
            (
                {
                    "function": f.qualified,
                    "file": f"llvm/{f.file}",
                    "line": f.line,
                    "why": why[k],
                    "rewrites": len(sites[k]),
                }
                for k, f in folds.items()
                if k in mine
            ),
            key=lambda r: (r["file"], r["line"], r["function"]),
        )
        others = [f for f in sc.functions[p] if id(f) not in folds and f.result in ("pointer", "bool")]
        out[p] = {
            "schema": schemas.REWRITES,
            "pass": p,
            "llvm": pins.llvm()["tag"],
            "rule": "docs/rewrite-inventory.md",
            "files": hashes,
            "entries": sorted({f.qualified for f in sc.entries(p)}),
            "totals": totals(rows),
            "folds": fold_rows,
            # Functions that return a value and aren't folds, for review: helpers decline but neither build IR
            # nor
            # are forwarded to; builders never decline, so a fold that returns what they build is the site.
            "helpers": sorted(
                {f.qualified for f in others if sc.info[id(f)]["declines"] and f.result == "pointer"}
            ),
            "builders": sorted(
                {f.qualified for f in others if not sc.info[id(f)]["declines"] and f.result == "pointer"}
            ),
            "rewrites": rows,
        }
    return out


def totals(rows: list[dict[str, Any]]) -> dict[str, Any]:
    by_need: Counter[str] = Counter()
    for r in rows:
        by_need["+".join(r["needs"])] += 1
    return {
        "rewrites": len(rows),
        "int": sum(1 for r in rows if r["needs"] == ["int"]),
        "blocked_fp": sum(1 for r in rows if "fp" in r["needs"]),
        "blocked_memory": sum(1 for r in rows if "memory" in r["needs"]),
        "blocked_calls": sum(1 for r in rows if "calls" in r["needs"]),
        "by_needs": dict(sorted(by_need.items())),
    }


def dump(doc: dict[str, Any]) -> str:
    """The inventory as JSON, one fold and one rewrite to a line, so a diff shows each that changed."""
    out = ["{"]
    items = list(doc.items())
    for n, (k, v) in enumerate(items):
        comma = "," if n + 1 < len(items) else ""
        if isinstance(v, list) and v and isinstance(v[0], dict):
            rows = ",\n".join("    " + json.dumps(r, ensure_ascii=False) for r in v)
            out.append(f"  {json.dumps(k)}: [\n{rows}\n  ]{comma}")
        else:
            body = json.dumps(v, indent=2, ensure_ascii=False).replace("\n", "\n  ")
            out.append(f"  {json.dumps(k)}: {body}{comma}")
    out.append("}")
    return "\n".join(out) + "\n"


def load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text()) if path.exists() else {}


def differences(old: dict[str, Any], new: dict[str, Any]) -> list[str]:
    """What changed from the recorded inventory `old` to the derived `new`, rewrite by rewrite."""
    bad = []
    for p, doc in new.items():
        was_doc = old.get(p) or {}
        if was_doc and dump(was_doc) == dump(doc):
            continue
        was = {r["id"]: r for r in was_doc.get("rewrites", [])}
        now = {r["id"]: r for r in doc["rewrites"]}
        found = []
        for i in sorted(now.keys() - was.keys()):
            found.append(f"{p}: new rewrite {i} at {now[i]['file']}:{now[i]['line']}")
        for i in sorted(was.keys() - now.keys()):
            found.append(f"{p}: rewrite {i} is gone from {was[i]['file']}:{was[i]['line']}")
        for i in sorted(now.keys() & was.keys()):
            if now[i] != was[i]:
                keys = sorted(k for k in now[i].keys() | was[i].keys() if now[i].get(k) != was[i].get(k))
                found.append(f"{p}: rewrite {i} changed: {', '.join(keys)}")
        if not found:
            keys = sorted(k for k in doc.keys() | was_doc.keys() if doc.get(k) != was_doc.get(k))
            found.append(f"{p}: {', '.join(keys) or 'the file'} differs from what the source gives")
        bad.extend(found)
    return bad


def source() -> Path:
    env = os.environ.get("LLVM_PROJECT_SRC")
    if not env or not (Path(env) / "llvm").is_dir():
        raise SystemExit(f"needs the dev shell, for LLVM_PROJECT_SRC: {env!r}")
    version = (Path(env) / "cmake" / "Modules" / "LLVMVersion.cmake").read_text()
    parts = [re.search(rf"set\(LLVM_VERSION_{k} (\d+)\)", version) for k in ("MAJOR", "MINOR", "PATCH")]
    got = ".".join(m.group(1) if m else "?" for m in parts)  # type: ignore[union-attr]
    if got != pins.llvm_version():
        raise SystemExit(f"LLVM_PROJECT_SRC is {got}, not the pinned {pins.llvm_version()}")
    return Path(env) / "llvm"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("generate")
    sub.add_parser("check")
    sm = sub.add_parser("summary")
    sm.add_argument("--json", action="store_true")
    args = ap.parse_args()
    if args.cmd in ("generate", "check"):
        inv = inventory(source())
        if args.cmd == "generate":
            HERE.mkdir(parents=True, exist_ok=True)
            for p, doc in inv.items():
                (HERE / f"{p}.json").write_text(dump(doc))
            print(json.dumps({p: d["totals"] for p, d in inv.items()}, indent=2))
            return 0
        bad = differences({p: load(HERE / f"{p}.json") for p in inv}, inv)
        for b in bad:
            print(b)
        print(
            "ok"
            if not bad
            else f"{len(bad)} differences: run `tests/llvm_rewrites.py generate` and review the diff"
        )
        return 1 if bad else 0
    docs = {p: json.loads((HERE / f"{p}.json").read_text()) for p in PASSES}
    summary = {p: d["totals"] for p, d in docs.items()}
    if args.json:
        print(json.dumps(summary, indent=2))
    else:
        for p, t in summary.items():
            print(
                f"{p}: {t['rewrites']} rewrites, {t['int']} integer-only, {t['blocked_fp']} need floating "
                f"point, {t['blocked_memory']} memory, {t['blocked_calls']} calls"
            )
    return 0


if __name__ == "__main__":
    sys.exit(main())
