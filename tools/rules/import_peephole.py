#!/usr/bin/env python3
"""Imports the proved rewrites of the Peephole library, and of `IRLean.Generic`, as rules.

Chunk 1's rewrites are proved from lemmas about values: `Refines (Val.add (Val.sub b a ..) a ..) b`, and the
like, in tests/passes-proofs/peephole/Peephole/Lemmas and IRLean/Generic. Each such lemma is a rule if the
format can say it: its left side a pattern, its right side a replacement, and its hypotheses side conditions
on constants. This reads every lemma there whose conclusion is `Refines l r` or `l = r` with `l` an
instruction, writes each one the format holds to rules/src/peephole.json with a one-line proof in
rules/Rules/Imported.lean, and records why each of the others can't be said, in rules/import/peephole.json.
docs/rules.md has the counts.

A lemma is kept only if Lean then checks that it proves the statement the format generates for it, so the
reader here is trusted for nothing: a lemma it misreads is refused, with Lean's error as the reason.

usage: tools/rules/import_peephole.py [--check]

`--check` fails if the three files aren't what this writes now.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import tempfile
from pathlib import Path
from typing import Any, ClassVar

ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.append(str(ROOT / "tools"))
sys.path.insert(0, str(Path(__file__).resolve().parent))

import gen  # noqa: E402
import lang  # noqa: E402
from irlean import lean, proc, schemas  # noqa: E402

SOURCES = [
    *sorted((ROOT / "tests" / "passes-proofs" / "peephole" / "Peephole" / "Lemmas").glob("*.lean")),
    ROOT / "IRLean" / "Generic" / "Arith.lean",
    ROOT / "IRLean" / "Generic" / "Bitwise.lean",
]
OUT_RULES = ROOT / "rules" / "src" / "peephole.json"
OUT_PROOFS = ROOT / "rules" / "Rules" / "Imported.lean"
OUT_RECORD = ROOT / "rules" / "import" / "peephole.json"
STORE_INDEX = ROOT / "store" / "index.json"

LEAN_OP = {info.lean: op for op, info in lang.OPS.items()}
LEAN_OP["IRLean.select"] = "select"


class Refuse(Exception):
    """Why a lemma isn't a rule."""


# ------------------------------------------------------------------------------------------------------------
# Reading the lemmas


def module_of(path: Path) -> str:
    rel = path.relative_to(ROOT)
    parts = rel.with_suffix("").parts
    if parts[0] == "tests":
        parts = parts[3:]
    return ".".join(parts)


def theorems(path: Path) -> list[tuple[str, str]]:
    """Each theorem's full name and the text between its name and its `:=`."""
    text = path.read_text()
    out = []
    stack: list[str] = []
    position = 0
    for m in re.finditer(r"^(namespace|section|end|theorem)\b[ \t]*(\S*)", text, re.M):
        kind, name = m[1], m[2]
        if m.start() < position:
            continue
        if kind == "namespace":
            stack.append(name)
        elif kind == "section":
            stack.append("")
        elif kind == "end":
            if stack:
                stack.pop()
        else:
            end = text.find(":=", m.end())
            if end < 0:
                continue
            body = " ".join(text[m.end() : end].split())
            out.append((".".join([*(s for s in stack if s), name]), body))
            position = end
    return out


def split_statement(body: str) -> tuple[list[tuple[str, list[str], str]], str]:
    """The binder groups, each its bracket, names and type, and the conclusion."""
    groups = []
    i = 0
    while i < len(body):
        if body[i] in "({":
            close = {"(": ")", "{": "}"}[body[i]]
            depth, j = 0, i
            while j < len(body):
                if body[j] in "({[":
                    depth += 1
                elif body[j] in ")}]":
                    depth -= 1
                    if depth == 0:
                        break
                j += 1
            inner = body[i + 1 : j]
            if body[j] != close or " : " not in inner:
                raise Refuse(f"a binder this doesn't read: {inner}")
            names, ty = inner.split(" : ", 1)
            groups.append((body[i], names.split(), ty.strip()))
            i = j + 1
        elif body[i] == ":":
            return groups, body[i + 1 :].strip()
        elif body[i].isspace():
            i += 1
        else:
            raise Refuse(f"a statement this doesn't read: {body[i : i + 40]}")
    raise Refuse("no conclusion")


TOKEN = re.compile(r"\s*(\(|\)|~~~|&&&|\|\|\||\^\^\^|[-+%=<≤≠¬]|[^\s()~&|^+%=<≤≠¬-]+)")


def tree(text: str) -> Any:
    """`text` as nested lists: a list is a parenthesized group, or the whole."""
    tokens = TOKEN.findall(text)
    position = 0

    def group(top: bool) -> list[Any]:
        nonlocal position
        items: list[Any] = []
        while position < len(tokens):
            token = tokens[position]
            position += 1
            if token == "(":
                items.append(group(False))
            elif token == ")":
                if top:
                    raise Refuse(f"unbalanced: {text}")
                return items
            else:
                items.append(token)
        if not top:
            raise Refuse(f"unbalanced: {text}")
        return items

    return group(True)


class Reader:
    """One lemma, as a rule."""

    def __init__(self, groups: list[tuple[str, list[str], str]]) -> None:
        self.values: dict[str, str] = {}  # the lemma's name for a value, and the rule's
        self.consts: dict[str, str] = {}
        self.flags: set[str] = set()
        self.nats: set[str] = set()
        self.hyps: list[str] = []
        self.divs: dict[str, Any] = {}  # a value that's a division's result, and the division
        self.flag_sites: dict[tuple[str, ...], Any] = {}  # the instruction each set of flag variables is on
        self.shared: list[Any] = []  # instructions the left side names twice
        self.defined: dict[str, Any] = {}  # a constant a hypothesis defines, and its expression
        self.fixed: dict[str, int] = {}  # a value's width, where the lemma fixes it
        for _, names, ty in groups:
            if re.fullmatch(r"Val \w+", ty):
                for n in names:
                    self.values[n] = self.value_name(n)
                    if ty.split()[1].isdigit():
                        self.fixed[n] = int(ty.split()[1])
            elif re.fullmatch(r"BitVec \w+", ty):
                for n in names:
                    self.consts[n] = ""
            elif ty == "Bool":
                self.flags.update(names)
            elif ty == "Nat":
                self.nats.update(names)
            elif len(names) == 1:
                self.hyps.append(ty)
            else:
                raise Refuse(f"a binder this doesn't read: {' '.join(names)} : {ty}")
        taken = {c.upper() for c in self.consts if re.fullmatch(r"[cC]\d*", c)}
        fresh = (f"C{i}" for i in range(100))
        for c in self.consts:
            if re.fullmatch(r"[cC]\d*", c):
                self.consts[c] = c.upper()
            else:
                name = next(f for f in fresh if f not in taken)
                taken.add(name)
                self.consts[c] = name

    @staticmethod
    def value_name(name: str) -> str:
        up = name[0].upper() + name[1:].replace("'", "p")
        if re.fullmatch(r"C\d*", up) or up in ("W",) or re.fullmatch(r"[WFQH]\d+", up):
            up = "V" + up
        return up

    # -- constants

    # Lean's infix operators on `BitVec`, loosest first.
    LEVELS = (("|||",), ("^^^",), ("&&&",), ("+", "-"), ("%",))
    INFIX: ClassVar[dict[str, str]] = {
        "+": "c.add",
        "-": "c.sub",
        "&&&": "c.and",
        "|||": "c.or",
        "^^^": "c.xor",
        "%": "c.urem",
    }

    def const(self, items: Any) -> Any:
        """A `BitVec` expression, as a constant term."""
        if isinstance(items, str):
            items = [items]
        if len(items) == 1 and isinstance(items[0], list):
            return self.const(items[0])
        for level in self.LEVELS:
            for at in range(len(items) - 1, 0, -1):
                before = items[at - 1]
                if isinstance(items[at], str) and items[at] in level and before not in (*self.INFIX, "~~~"):
                    return lang.CExpr(
                        self.INFIX[items[at]], (self.const(items[:at]), self.const(items[at + 1 :]))
                    )
        if items[0] == "~~~" and len(items) >= 2:
            return lang.CExpr("c.not", (self.const(items[1:]),))
        if items[0] == "-" and len(items) >= 2:
            return lang.CExpr("c.neg", (self.const(items[1:]),))
        if len(items) == 1:
            token = items[0]
            m = re.fullmatch(r"(\d+)#(\w+)", token)
            if m:
                return lang.Lit(int(m[1]))
            if token in self.defined:
                return self.defined[token]
            if token in self.consts:
                return lang.CVar(self.consts[token])
            raise Refuse(f"a constant this doesn't read: {token}")
        if len(items) == 2 and items[0] in ("BitVec.allOnes", "BitVec.intMin", "BitVec.intMax"):
            return lang.Lit(
                {"BitVec.allOnes": -1, "BitVec.intMin": "intmin", "BitVec.intMax": "intmax"}[items[0]]
            )
        if len(items) == 2 and isinstance(items[0], str) and items[0].endswith(".srem"):
            return lang.CExpr("c.srem", (self.const(items[0][: -len(".srem")]), self.const(items[1])))
        raise Refuse(f"a constant this doesn't read: {flat(items)}")

    # -- values

    def value(self, items: Any, pattern: bool) -> Any:
        if isinstance(items, str):
            items = [items]
        if len(items) == 1 and isinstance(items[0], list):
            return self.value(items[0], pattern)
        head = items[0]
        if len(items) == 1:
            if head in self.divs:
                return self.divs[head] if pattern else lang.Var(self.values[head])
            if head in self.values:
                return lang.Var(self.values[head], self.fixed.get(head) if pattern else None)
            if head == "none":
                raise Refuse("poison as an operand, which no pattern matches")
            raise Refuse(f"a value this doesn't read: {head}")
        if head == "some" and len(items) == 2:
            return self.const(items[1])
        if head == "Outcome.ok" and len(items) == 2 and not pattern:
            return self.value(items[1], pattern)
        if not isinstance(head, str) or (head not in LEAN_OP and head != "select"):
            raise Refuse(f"an operation the format doesn't have: {flat(items)[:60]}")
        op = LEAN_OP.get(head, "select")
        info = lang.OPS[op]
        rest = items[1:]
        if info.kind == "cast":
            rest = rest[1:]  # the width it casts to, which the pattern's types give
        if len(rest) < info.arity or len(rest) > info.arity + len(info.flags):
            raise Refuse(f"{head} with {len(rest)} operands")
        args = tuple(self.value(a, pattern) for a in rest[: info.arity])
        given = rest[info.arity :]
        set_flags = []
        variables = []
        for i, flag in enumerate(info.flags):
            f = given[i] if i < len(given) else "false"
            if f == "true":
                set_flags.append(flag)
            elif f == "false":
                if pattern:
                    raise Refuse(f"the pattern needs {flag} unset on {op}, which the format can't ask")
            elif isinstance(f, str) and f in self.flags:
                if not pattern:
                    raise Refuse(f"the replacement's {flag} depends on a matched flag")
                variables.append(f)
            else:
                raise Refuse(f"a flag this doesn't read: {flat(f)}")
        node = lang.App(op, tuple(set_flags), args)
        if variables:
            # One flag variable names one instruction's flag: the same instruction again, or it isn't a
            # pattern.
            for site, at in self.flag_sites.items():
                if set(site) & set(variables):
                    if site != tuple(variables) or at != node:
                        raise Refuse("one flag variable on two instructions")
                    if node not in self.shared:
                        self.shared.append(node)
            self.flag_sites[tuple(variables)] = node
        return node

    # -- hypotheses

    def hypothesis(self, text: str) -> str | None:
        """A hypothesis as a side condition, or None if it's a division's result, which the pattern takes."""
        items = tree(text)
        if (
            "=" in items
            and items[:1]
            and isinstance(items[0], str)
            and items[0] in ("Val.udiv", "Val.sdiv", "Val.urem", "Val.srem")
        ):
            eq = items.index("=")
            right = items[eq + 1 :]
            if len(right) == 2 and right[0] == "Outcome.ok" and right[1] in self.values:
                self.divs[right[1]] = None  # set by the caller, once every division is known
                self.pending.append((right[1], items[:eq]))
                return None
        if "∀" in text or "→" in text:
            raise Refuse(f"a hypothesis about a value, which takes an analysis: {text}")
        if re.fullmatch(r"(\d+) < w", text):
            return f"(wgt {text.split()[0]})"
        words = set(re.findall(r"[\w']+", text))
        if words & self.flags:
            raise Refuse(f"a hypothesis about a flag: {text}")
        if words & set(self.values):
            raise Refuse(f"a hypothesis about a value, which takes an analysis: {text}")
        if len(items) == 3 and items[1] == "≤" and {items[0], items[2]} <= self.nats | {"w"}:
            return None  # a cast's operand is narrower than its result, which the statement says itself
        if (
            len(items) >= 3
            and items[-2] == "="
            and items[-1] in self.consts
            and items[-1] not in self.in_pattern
        ):
            self.defined[items[-1]] = self.const(items[:-2])
            return None
        try:
            return self.condition(items)
        except Refuse as error:
            raise Refuse(f"a hypothesis the format has no side condition for: {text}") from error

    def condition(self, items: Any) -> str:
        negated = bool(items) and items[0] == "¬"
        if negated:
            items = items[1:]
        out = None
        if len(items) == 1 and isinstance(items[0], str):
            m = re.fullmatch(r"(\w+)\.toNat\.isPowerOfTwo", items[0])
            if m and m[1] in self.consts:
                out = f"(pow2 {self.consts[m[1]]})"
        if len(items) == 2 and isinstance(items[0], str) and items[0].endswith((".ule", ".sle")):
            name = "bule" if items[0].endswith(".ule") else "bsle"
            out = f"({name} {lang.show(self.const(items[0][:-4]))} {lang.show(self.const(items[1]))})"
        for op, name in (("=", "eq"), ("≠", "ne"), ("<", "ult"), ("≤", "ule")):
            if out is None and op in items:
                at = items.index(op)
                left, right = items[:at], items[at + 1 :]
                if name == "eq" and right == ["true"] and len(left) == 1 and isinstance(left[0], str):
                    m = re.fullmatch(r"(\w+)\.msb", left[0])
                    if m and m[1] in self.consts:
                        out = f"(msb {self.consts[m[1]]})"
                        break
                if name == "eq" and right == ["true"] and len(left) == 2 and left[1] == "0":
                    m = re.fullmatch(r"(\w+)\.getLsbD", str(left[0]))
                    if m and m[1] in self.consts:
                        out = f"(lsb {self.consts[m[1]]})"
                        break
                out = f"({name} {lang.show(self.const(left))} {lang.show(self.const(right))})"
                break
        if out is None:
            raise Refuse(f"a hypothesis the format has no side condition for: {flat(items)}")
        return f"(not {out})" if negated else out

    def rule(self, conclusion: str) -> dict[str, Any]:
        items = tree(conclusion)
        if items and items[0] == "Refines" and len(items) == 3:
            left, right, kind = items[1], items[2], "refines"
        elif "=" in items:
            at = items.index("=")
            left, right, kind = items[:at], items[at + 1 :], "eq"
        else:
            raise Refuse("its conclusion isn't a refinement or an equation of two values")
        self.pending: list[tuple[str, Any]] = []
        self.in_pattern = set(re.findall(r"[\w']+", flat(left)))
        where = [c for c in (self.hypothesis(h) for h in self.hyps) if c is not None]
        for name, division in self.pending:
            self.divs[name] = lang.Bind(self.values[name], self.value(division, True))
        pattern = self.value(left, True)
        if not isinstance(pattern, lang.App):
            raise Refuse("its left side isn't an instruction")
        pattern = self.share(pattern)
        try:
            replacement = self.value(right, False)
        except Refuse:
            # The right side may be something the left side matched, flags and all.
            replacement = self.matched(pattern, right)
            if replacement is None:
                raise
            pattern, name = replacement
            replacement = lang.Var(name)
        # A division's result used once is the division itself, not a name for it.
        pattern = self.unbind(pattern, replacement)
        return {"match": lang.show(pattern), "replace": lang.show(replacement), "where": where, "kind": kind}

    def share(self, pattern: Any) -> Any:
        """The pattern with each instruction it names twice bound the first time, and used by name after."""
        names: dict[Any, str] = {}

        def go(node: Any) -> Any:
            if isinstance(node, lang.App) and node in self.shared:
                if node in names:
                    return lang.Var(names[node])
                names[node] = f"S{len(names)}"
                return lang.Bind(names[node], lang.App(node.op, node.flags, tuple(go(a) for a in node.args)))
            if isinstance(node, lang.App):
                return lang.App(node.op, node.flags, tuple(go(a) for a in node.args))
            if isinstance(node, lang.Bind):
                return lang.Bind(node.name, go(node.term))
            return node

        return go(pattern)

    def matched(self, pattern: Any, right: Any) -> tuple[Any, str] | None:
        """If the right side is an instruction of the pattern, the pattern with that instruction bound."""
        sites, shared = dict(self.flag_sites), list(self.shared)
        try:
            target = self.value(right, True)
        except Refuse:
            return None
        finally:
            self.flag_sites, self.shared = sites, shared
        name = "T"
        found = False

        def go(node: Any) -> Any:
            nonlocal found, name
            if isinstance(node, lang.Bind) and node.term == target and not found:
                found = True
                name = node.name
                return node
            if node == target and not found and isinstance(node, lang.App):
                found = True
                return lang.Bind(name, node)
            if isinstance(node, lang.App):
                return lang.App(node.op, node.flags, tuple(go(a) for a in node.args))
            if isinstance(node, lang.Bind):
                return lang.Bind(node.name, go(node.term))
            return node

        new = lang.App(pattern.op, pattern.flags, tuple(go(a) for a in pattern.args))
        return (new, name) if found else None

    def unbind(self, pattern: Any, replacement: Any) -> Any:
        used: set[str] = set()

        def names(node: Any) -> None:
            if isinstance(node, lang.Var):
                used.add(node.name)
            elif isinstance(node, lang.App | lang.CExpr):
                for a in node.args:
                    names(a)

        names(replacement)

        def again(node: Any) -> None:
            if isinstance(node, lang.Var):
                used.add(node.name)
            elif isinstance(node, lang.App):
                for a in node.args:
                    again(a)
            elif isinstance(node, lang.Bind):
                again(node.term)

        again(pattern)

        def go(node: Any) -> Any:
            if isinstance(node, lang.Bind):
                inner = go(node.term)
                return lang.Bind(node.name, inner) if node.name in used else inner
            if isinstance(node, lang.App):
                return lang.App(node.op, node.flags, tuple(go(a) for a in node.args))
            return node

        return go(pattern)


def flat(items: Any) -> str:
    if isinstance(items, str):
        return items
    return " ".join(f"({flat(i)})" if isinstance(i, list) else i for i in items)


# ------------------------------------------------------------------------------------------------------------
# The import


def candidates() -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    """Each lemma read as a rule, and each that can't be, with why. Lemmas whose conclusion isn't about an
    instruction at all aren't rewrites, and aren't listed."""
    index = json.loads(STORE_INDEX.read_text())
    sites = {e["name"]: e.get("rewrites", []) for e in index["lemmas"]}
    read: list[dict[str, Any]] = []
    refused: list[dict[str, Any]] = []
    seen: dict[tuple[str, str, tuple[str, ...]], str] = {}
    names: set[str] = set()
    for path in SOURCES:
        for full, body in theorems(path):
            short = full.rsplit(".", 1)[-1]
            if ".Counter." in full or short.startswith("drop_") or short == "sat":
                continue
            try:
                groups, conclusion = split_statement(body)
            except Refuse:
                continue
            head = conclusion.split("(")[0].strip()
            lhs = (
                conclusion.split("=")[0].strip()
                if head != "Refines"
                else conclusion[len("Refines") :].strip()
            )
            if not (head == "Refines" or re.match(r"(Val\.\w+|select) ", lhs)) or not re.match(
                r"\(?(Val\.\w+|select) ", lhs
            ):
                continue
            entry: dict[str, Any] = {"lemma": full, "module": module_of(path)}
            try:
                raw = Reader(groups).rule(conclusion)
                name = re.sub(r"_refines(?=_|$)", "", short)
                key = (raw["match"], raw["replace"], tuple(raw["where"]))
                if key in seen:
                    raise Refuse(f"the same rule as {seen[key]}")
                if name in names:
                    name = short
                while name in names:
                    name += "_b"
                rule = {"name": name, "match": raw["match"], "replace": raw["replace"]}
                if raw["where"]:
                    rule["where"] = raw["where"]
                rule["from"] = full
                if sites.get(full):
                    rule["sites"] = sites[full]
                lang.Rule(rule)
                seen[key] = name
                names.add(name)
                read.append({**entry, "rule": rule, "kind": raw["kind"]})
            except (Refuse, lang.RuleError) as error:
                refused.append({**entry, "reason": str(error)})
    return read, refused


def proof(entry: dict[str, Any]) -> str:
    tactic = "rule_from" if entry["kind"] == "refines" else "rule_from_eq"
    return f"theorem {entry['rule']['name']} : Stmt.{entry['rule']['name']} := by {tactic} {entry['lemma']}\n"


def proofs_text(entries: list[dict[str, Any]]) -> str:
    modules = sorted({e["module"] for e in entries})
    return (
        "import Rules.Mono\nimport Rules.Statements\n"
        + "".join(f"import {m}\n" for m in modules)
        + "\n/-! # The imported rules' proofs\n\n"
        "Written by `tools/rules/import_peephole.py`, one line a rule: the lemma the rule was read from\n"
        "proves the statement `tools/rules/rules.py gen` generates for it. Do not edit:\n"
        "`import_peephole.py --check` fails if this isn't what it writes. -/\n\nnamespace Rules\n\n"
        + "".join(proof(e) for e in entries)
        + "\nend Rules\n"
    )


def lean_checks(entries: list[dict[str, Any]]) -> dict[str, str]:
    """Each entry's name whose proof Lean refuses, with its first error."""
    with tempfile.TemporaryDirectory(dir=ROOT / "build") as temporary:
        work = Path(temporary)
        (work / "Rules").mkdir()
        (work / "Rules" / "Mono.lean").write_text((ROOT / "rules" / "Rules" / "Mono.lean").read_text())
        rules = [lang.Rule(e["rule"]) for e in entries]
        (work / "Rules" / "Statements.lean").write_text(gen.statements_text(rules))
        (work / "Rules" / "Imported.lean").write_text(proofs_text(entries))
        env = lean.env(work, pin=True)
        for module in ("Mono", "Statements"):
            ran = proc.run(
                lean.argv(4096, "-o", f"Rules/{module}.olean", f"Rules/{module}.lean"),
                cwd=work,
                env=env,
                timeout=600,
                cap_mb=4500,
            )
            if ran.exit != 0:
                raise RuntimeError(f"Rules/{module}.lean doesn't compile:\n{ran.output[:4000]}")
        ran = proc.run(lean.argv(4096, "Rules/Imported.lean"), cwd=work, env=env, timeout=900, cap_mb=4500)
        if ran.limit is not None:
            raise RuntimeError(f"checking the imported proofs was stopped: {ran.limit}")
        lines = (work / "Rules" / "Imported.lean").read_text().splitlines()
        failed: dict[str, str] = {}
        for message in lean.messages(ran.output):
            if message.severity != "error":
                continue
            m = re.match(r"theorem (\w+) ", lines[message.line - 1]) if message.line <= len(lines) else None
            if m is None:
                raise RuntimeError(f"an error outside a proof:\n{ran.output[:4000]}")
            failed.setdefault(m[1], " ".join(message.text.split())[:300])
        return failed


def build() -> tuple[str, str, str]:
    read, refused = candidates()
    failed = lean_checks(read)
    kept = [e for e in read if e["rule"]["name"] not in failed]
    for e in read:
        if e["rule"]["name"] in failed:
            refused.append(
                {
                    "lemma": e["lemma"],
                    "module": e["module"],
                    "reason": f"Lean doesn't accept the lemma as a proof of the generated statement: "
                    f"{failed[e['rule']['name']]}",
                }
            )
    refused.sort(key=lambda e: e["lemma"])
    source = {"schema": schemas.RULES, "rules": [e["rule"] for e in kept]}
    record = {
        "schema": schemas.RULES_IMPORT,
        "sources": [str(p.relative_to(ROOT)) for p in SOURCES],
        "considered": len(kept) + len(refused),
        "imported": [{"lemma": e["lemma"], "rule": e["rule"]["name"]} for e in kept],
        "refused": [{"lemma": e["lemma"], "reason": e["reason"]} for e in refused],
    }
    return (
        schemas.dumps(source, schemas.RULES, indent=1, ensure_ascii=False) + "\n",
        proofs_text(kept),
        schemas.dumps(record, schemas.RULES_IMPORT, indent=1, ensure_ascii=False) + "\n",
    )


def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    texts = build()
    stale = []
    for path, text in zip((OUT_RULES, OUT_PROOFS, OUT_RECORD), texts, strict=True):
        if args.check:
            if not path.exists() or path.read_text() != text:
                stale.append(str(path.relative_to(ROOT)))
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
    record = json.loads(texts[2])
    print(
        f"{record['considered']} lemmas considered, {len(record['imported'])} imported as rules, "
        f"{len(record['refused'])} refused"
    )
    if stale:
        print("FAIL  not what import_peephole.py writes now: " + ", ".join(stale))
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
