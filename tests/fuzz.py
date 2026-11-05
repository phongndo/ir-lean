#!/usr/bin/env python3
"""Generates random integer functions with branches, loops and switches, optimizes them at random
levels, and compares emitted Lean with native code.

usage: tests/fuzz.py path/to/llvm-lean [--seeds N] [--functions N] [--start S]
"""
import os
import random
import shutil
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import differential  # noqa: E402

WIDTHS = [8, 16, 32, 64]
BINOPS = ["add", "sub", "mul", "and", "or", "xor", "shl", "lshr", "ashr"]
FLAGS = {"add": ["nuw", "nsw"], "sub": ["nuw", "nsw"], "mul": ["nuw", "nsw"], "shl": ["nuw", "nsw"],
         "lshr": ["exact"], "ashr": ["exact"]}
PREDS = "eq ne ugt uge ult ule sgt sge slt sle".split()
INTRINSICS2 = "umin umax smin smax uadd.sat usub.sat sadd.sat ssub.sat".split()
INTRINSICS1 = "ctpop bitreverse".split()


class Gen:
    """Builds SSA directly. `env` maps variable index to (ssa name, width)."""

    def __init__(self, rand):
        self.r = rand
        self.lines = []
        self.next_value = 0
        self.next_block = 0
        self.block = "entry"
        self.decls = set()

    def fresh(self):
        self.next_value += 1
        return f"%v{self.next_value}"

    def label(self, stem):
        self.next_block += 1
        return f"{stem}{self.next_block}"

    def emit(self, text):
        self.lines.append("  " + text)

    def start(self, label):
        self.lines.append(f"{label}:")
        self.block = label

    def const(self, w):
        m = (1 << w) - 1
        return self.r.choice([0, 1, 2, 3, 7, m, 1 << (w - 1), self.r.getrandbits(w)])

    def as_width(self, value, w_from, w_to):
        if w_from == w_to:
            return value
        v = self.fresh()
        if w_to > w_from:
            self.emit(f"{v} = {self.r.choice(['zext', 'sext'])} i{w_from} {value} to i{w_to}")
        else:
            self.emit(f"{v} = trunc i{w_from} {value} to i{w_to}")
        return v

    def pick(self, env, w):
        if self.r.random() < 0.25:
            return str(self.const(w))
        name, width = self.r.choice(list(env.values()))
        return self.as_width(name, width, w)

    def condition(self, env):
        w = self.r.choice(WIDTHS)
        a, b = self.pick(env, w), self.pick(env, w)
        c = self.fresh()
        self.emit(f"{c} = icmp {self.r.choice(PREDS)} i{w} {a}, {b}")
        return c

    def assign(self, env):
        target = self.r.choice(list(env))
        w = env[target][1]
        kind = self.r.random()
        v = self.fresh()
        if kind < 0.6:
            op = self.r.choice(BINOPS)
            a, b = self.pick(env, w), self.pick(env, w)
            if op in ("shl", "lshr", "ashr"):
                m = self.fresh()
                self.emit(f"{m} = and i{w} {b}, {w - 1}")
                b = m
            flags = ""
            if op in FLAGS and self.r.random() < 0.15:
                flags = self.r.choice(FLAGS[op])
            self.emit(f"{v} = {op} {flags} i{w} {a}, {b}".replace("  ", " "))
        elif kind < 0.72:
            op = self.r.choice(["udiv", "urem", "sdiv", "srem"])
            a, b = self.pick(env, w), self.pick(env, w)
            m = self.fresh()
            # Mostly nonzero divisors, so most runs still reach the end.
            self.emit(f"{m} = or i{w} {b}, {self.r.choice([1, 1, 1, 2])}")
            self.emit(f"{v} = {op} i{w} {a}, {m}")
        elif kind < 0.84:
            c = self.condition(env)
            a, b = self.pick(env, w), self.pick(env, w)
            self.emit(f"{v} = select i1 {c}, i{w} {a}, i{w} {b}")
        elif kind < 0.92:
            name = self.r.choice(INTRINSICS2)
            self.decls.add(f"declare i{w} @llvm.{name}.i{w}(i{w}, i{w})")
            a, b = self.pick(env, w), self.pick(env, w)
            self.emit(f"{v} = call i{w} @llvm.{name}.i{w}(i{w} {a}, i{w} {b})")
        else:
            name = self.r.choice(INTRINSICS1)
            self.decls.add(f"declare i{w} @llvm.{name}.i{w}(i{w})")
            a = self.pick(env, w)
            self.emit(f"{v} = call i{w} @llvm.{name}.i{w}(i{w} {a})")
        return {**env, target: (v, w)}

    def merge(self, env_base, arms, label):
        """`arms` are (block, env) pairs that branch to `label`. Returns the env after phis."""
        self.start(label)
        merged = {}
        for key, (_, w) in env_base.items():
            names = [(block, env[key][0]) for block, env in arms]
            if len({n for _, n in names}) == 1:
                merged[key] = (names[0][1], w)
            else:
                v = self.fresh()
                incoming = ", ".join(f"[ {n}, %{b} ]" for b, n in names)
                self.emit(f"{v} = phi i{w} {incoming}")
                merged[key] = (v, w)
        return merged

    def statements(self, env, depth):
        for _ in range(self.r.randint(1, 4)):
            roll = self.r.random()
            if depth > 0 and roll < 0.18:
                env = self.branch(env, depth)
            elif depth > 0 and roll < 0.30:
                env = self.counted_loop(env, depth)
            elif depth > 0 and roll < 0.36:
                env = self.switch(env, depth)
            else:
                env = self.assign(env)
        return env

    def branch(self, env, depth):
        then, other, end = self.label("then"), self.label("else"), self.label("end")
        c = self.condition(env)
        self.emit(f"br i1 {c}, label %{then}, label %{other}")
        self.start(then)
        env1 = self.statements(env, depth - 1)
        block1 = self.block
        self.emit(f"br label %{end}")
        self.start(other)
        env2 = self.statements(env, depth - 1)
        block2 = self.block
        self.emit(f"br label %{end}")
        return self.merge(env, [(block1, env1), (block2, env2)], end)

    def switch(self, env, depth):
        w = self.r.choice(WIDTHS)
        sel = self.pick(env, w)
        end = self.label("end")
        default, cases = self.label("default"), [self.label("case") for _ in range(self.r.randint(1, 3))]
        keys = self.r.sample(range(8), len(cases))
        table = " ".join(f"i{w} {k}, label %{c}" for k, c in zip(keys, cases))
        self.emit(f"switch i{w} {sel}, label %{default} [ {table} ]")
        arms = []
        for label in [default] + cases:
            self.start(label)
            e = self.statements(env, depth - 1)
            arms.append((self.block, e))
            self.emit(f"br label %{end}")
        return self.merge(env, arms, end)

    def counted_loop(self, env, depth):
        pre = self.block
        head, body, end = self.label("head"), self.label("body"), self.label("end")
        limit = self.r.randint(1, 6)
        self.emit(f"br label %{head}")
        self.start(head)
        counter, next_counter = self.fresh(), self.fresh()
        phis, placeholders = {}, []
        for key, (name, w) in env.items():
            v = self.fresh()
            phis[key] = (v, w)
            placeholders.append((len(self.lines), v, w, name, key))
            self.lines.append("")
        back = f"%BACK_{head}"
        self.emit(f"{counter} = phi i32 [ 0, %{pre} ], [ {next_counter}, {back} ]")
        done = self.fresh()
        self.emit(f"{done} = icmp uge i32 {counter}, {limit}")
        self.emit(f"br i1 {done}, label %{end}, label %{body}")
        self.start(body)
        env_body = self.statements(phis, depth - 1)
        latch = self.block
        self.emit(f"{next_counter} = add i32 {counter}, 1")
        self.emit(f"br label %{head}")
        for pos, v, w, name, key in placeholders:
            self.lines[pos] = f"  {v} = phi i{w} [ {name}, %{pre} ], [ {env_body[key][0]}, %{latch} ]"
        for i, line in enumerate(self.lines):
            if back in line:
                self.lines[i] = line.replace(back, f"%{latch}")
        self.start(end)
        return phis


def function(name, rand, decls):
    g = Gen(rand)
    widths = [rand.choice(WIDTHS) for _ in range(rand.randint(1, 3))]
    env = {i: (f"%a{i}", w) for i, w in enumerate(widths)}
    for extra in range(rand.randint(0, 2)):
        w = rand.choice(WIDTHS)
        env[len(widths) + extra] = (str(g.const(w)), w)
    env = g.statements(env, 3)
    ret = rand.choice(WIDTHS)
    result = g.pick(env, ret)
    g.emit(f"ret i{ret} {result}")
    decls.update(g.decls)
    params = ", ".join(f"i{w} %a{i}" for i, w in enumerate(widths))
    return f"define i{ret} @{name}({params}) {{\nentry:\n" + "\n".join(g.lines) + "\n}\n"


def main():
    args = sys.argv[1:]
    def flag(name, default):
        if name in args:
            i = args.index(name)
            value = int(args[i + 1])
            del args[i:i + 2]
            return value
        return default
    seeds = flag("--seeds", 5)
    per_module = flag("--functions", 30)
    start = flag("--start", 1)
    tool = os.path.abspath(args[0])
    levels = [None, "default<O1>", "default<O2>", "default<O3>"]
    stats = differential.Stats()
    work = tempfile.mkdtemp(prefix="fuzz-")
    try:
        for seed in range(start, start + seeds):
            rand = random.Random(seed)
            decls, funcs = set(), []
            for i in range(per_module):
                funcs.append(function(f"f{i}", rand, decls))
            ll = os.path.join(work, f"s{seed}.ll")
            with open(ll, "w") as f:
                f.write("\n".join(sorted(decls)) + "\n\n" + "\n".join(funcs))
            subprocess.run(["opt", "-passes=verify", "-disable-output", ll], check=True)
            level = levels[seed % len(levels)]
            if level:
                optimized = ll + ".opt.ll"
                subprocess.run(["opt", f"-passes={level}", "-S", ll, "-o", optimized], check=True)
                ll = optimized
            differential.compare_ll(tool, ll, 12, rand, stats)
    finally:
        keep = bool(stats.mismatches)
        if keep:
            print(f"kept generated modules in {work}")
        else:
            shutil.rmtree(work, ignore_errors=True)
    sys.exit(differential.summarize(stats))


if __name__ == "__main__":
    main()
