"""x86's intrinsics in the model, as operations for the tests that check them: tests/x86native.py against the
processor, and tests/x86check.py against Alive2 and LLVM's constant folder. docs/x86-intrinsics.md says what
each is checked against.

Each form of an intrinsic is one operation, and a form with an immediate is one for each immediate tried.
`covered` is every intrinsic an operation here calls, which tests/x86native.py compares with what the
classification says is modeled, so a modeled x86 intrinsic can't go unchecked against the processor.

tests/x86/Wrong.lean has a wrong version of each definition these call. A check has to refuse it: the
processor has to disagree with it on some input to each intrinsic, and so does Alive2, or the constant folder,
where it knows the intrinsic.
"""

from __future__ import annotations

import itertools
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from vecopcheck import TERNLOG, X86, x86_shapes

ROOT = Path(__file__).resolve().parent.parent
WRONG = ROOT / "tests" / "x86" / "Wrong.lean"
POISON = -1
Shape = tuple[int, int]

# What the native check's code is compiled for, and the flag /proc/cpuinfo has for each.
FEATURES = {
    "sse4.2": "sse4_2",
    # LLVM selects the CRC32 instruction under a feature of its own, which SSE4.2 processors have.
    "crc32": "sse4_2",
    "avx2": "avx2",
    "avx512f": "avx512f",
    "avx512bw": "avx512bw",
    "avx512vl": "avx512vl",
    "avx512vnni": "avx512_vnni",
    "pclmul": "pclmulqdq",
    "vpclmulqdq": "vpclmulqdq",
    "aes": "aes",
    "vaes": "vaes",
    "bmi": "bmi1",
    "bmi2": "bmi2",
    "gfni": "gfni",
}


@dataclass(frozen=True)
class Op:
    intrinsic: str
    # (lanes, width) of the result and of each operand. A scalar has 0 lanes.
    ret: Shape
    args: tuple[Shape, ...]
    # A last operand that has to be a constant: its type and value.
    imm: tuple[str, int] | None = None
    # How to pick each operand's lanes: "" for any value, for a shift's count, "count" in each lane and
    # "count64" in a vector's low 64 bits, and "bytes" to also try every byte value, for a table of them.
    picks: tuple[str, ...] = ()
    # Whether the pinned Alive2 knows the intrinsic, and whether InstCombine folds a call on constants.
    alive: bool = False
    folds: bool = False
    # For an operation that isn't one call: the instructions that define %r, and what they declare. And the
    # target features to compile native code for, optimized, so that its values are in registers. `tag` tells
    # two operations on one intrinsic apart.
    body: str = ""
    declares: str = ""
    optimized: str = ""
    tag: str = ""
    # Whether tests/x86/Wrong.lean has a wrong version of what it calls.
    mutant: bool = True

    @property
    def name(self) -> str:
        """The function that calls it, in a test's module."""
        suffix = self.tag if self.imm is None else f"_{self.imm[1]}"
        return "x86_" + re.sub(r"\W", "_", self.intrinsic.removeprefix("llvm.x86.")) + suffix

    def pick(self, i: int) -> str:
        return self.picks[i] if i < len(self.picks) else ""

    @property
    def declaration(self) -> str:
        if self.declares:
            return self.declares
        types = [ty(a) for a in self.args] + ([f"{self.imm[0]} immarg"] if self.imm else [])
        return f"declare {ty(self.ret)} @{self.intrinsic}({', '.join(types)})"

    @property
    def call(self) -> str:
        """The call, on %a0, %a1 and so on."""
        operands = [f"{ty(a)} %a{i}" for i, a in enumerate(self.args)]
        if self.imm:
            operands.append(f"{self.imm[0]} {self.imm[1]}")
        return f"call {ty(self.ret)} @{self.intrinsic}({', '.join(operands)})"

    @property
    def definition(self) -> str:
        params = ", ".join(f"{ty(a)} %a{i}" for i, a in enumerate(self.args))
        ret = ty(self.ret)
        return f"define {ret} @{self.name}({params}) {{\n  {self.lines}\n  ret {ret} %r\n}}\n"

    @property
    def lines(self) -> str:
        """The instructions that define %r."""
        return self.body or f"%r = {self.call}"


def ty(shape: Shape) -> str:
    return f"i{shape[1]}" if shape[0] == 0 else f"<{shape[0]} x i{shape[1]}>"


def bits(intrinsic: str) -> int:
    """The width of an intrinsic's vectors, from its name."""
    if m := re.search(r"\.(128|256|512)$", intrinsic):
        return int(m[1])
    return 256 if ".avx2." in intrinsic else 128


def dot_products() -> list[Op]:
    """IRLean/X86.lean. Alive2 and InstCombine know the first two."""
    ops = []
    for name in ("ssse3.pmadd.ub.sw.128", "avx2.pmadd.ub.sw", "avx512.pmaddubs.w.512"):
        n = bits(f"llvm.x86.{name}") // 8
        ops.append(Op(f"llvm.x86.{name}", (n // 2, 16), ((n, 8), (n, 8)), alive=True, folds=True))
    for name in ("sse2.pmadd.wd", "avx2.pmadd.wd", "avx512.pmaddw.d.512"):
        n = bits(f"llvm.x86.{name}") // 16
        ops.append(Op(f"llvm.x86.{name}", (n // 2, 32), ((n, 16), (n, 16)), alive=True, folds=True))
    for width in (128, 256, 512):
        acc, b = (width // 32, 32), (width // 8, 8)
        ops.append(Op(f"llvm.x86.avx512.vpdpbusd.{width}", acc, (acc, b, b)))
    return ops


def bit_functions() -> list[Op]:
    """IRLean/X86Bits.lean: VPTERNLOG, PSHUFB and the shifts, which tests/vecopcheck.py checks against Alive2
    and the constant folder."""
    ops = []
    for enum in X86:
        name = "llvm." + enum.replace("_", ".")
        a, b = x86_shapes(enum)
        if "pternlog" in enum:
            ops += [Op(name, a, (a, a, a), ("i32", imm)) for imm in TERNLOG]
        elif "pshuf" in enum:
            ops.append(Op(name, a, (a, b)))
        else:
            count = "count" if b == a or b == (0, 32) else "count64"
            ops.append(Op(name, a, (a, b), picks=("", count)))
    return ops


def carry_less() -> list[Op]:
    """IRLean/X86Crypto.lean: PCLMULQDQ, with each quadword it can pick, and immediates whose other bits are
    set, which it doesn't read."""
    ops = []
    for name in ("llvm.x86.pclmulqdq", "llvm.x86.pclmulqdq.256", "llvm.x86.pclmulqdq.512"):
        a = (bits(name) // 64, 64)
        ops += [Op(name, a, (a, a), ("i8", imm)) for imm in (0x00, 0x01, 0x10, 0x11, 0xEE, 0xFF)]
    return ops


def aes() -> list[Op]:
    """IRLean/X86Crypto.lean: the AES rounds, with every byte value, so every entry of both S-boxes is
    checked."""
    ops = []
    for step in ("aesenc", "aesenclast", "aesdec", "aesdeclast"):
        for name in (f"llvm.x86.aesni.{step}", f"llvm.x86.aesni.{step}.256", f"llvm.x86.aesni.{step}.512"):
            a = (bits(name) // 64, 64)
            ops.append(Op(name, a, (a, a), picks=("bytes",)))
    ops.append(Op("llvm.x86.aesni.aesimc", (2, 64), ((2, 64),)))
    # Round constants, and an immediate with every bit set.
    for imm in (0x00, 0x01, 0x1B, 0x36, 0x80, 0xFF):
        ops.append(Op("llvm.x86.aesni.aeskeygenassist", (2, 64), ((2, 64),), ("i8", imm), picks=("bytes",)))
    return ops


def forms(stem: str, names: tuple[str, ...]) -> list[str]:
    """The intrinsics of one instruction: `{}` in `stem` replaced by each of `names`."""
    return [f"llvm.x86.{stem.format(name)}" for name in names]


def lanewise(names: list[str], w: int, operands: int = 2, **how: Any) -> list[Op]:
    """Intrinsics whose result and operands are all vectors of `w`-bit lanes."""
    return [Op(name, (bits(name) // w, w), ((bits(name) // w, w),) * operands, **how) for name in names]


# IRLean/X86Arith.lean, a family at a time. Alive2 knows most, and InstCombine folds some.
def averages() -> list[Op]:
    return lanewise(
        forms("{}", ("sse2.pavg.b", "avx2.pavg.b", "avx512.pavg.b.512")), 8, alive=True
    ) + lanewise(forms("{}", ("sse2.pavg.w", "avx2.pavg.w", "avx512.pavg.w.512")), 16, alive=True)


def packs() -> list[Op]:
    ops = []
    for u, names in (
        (16, ("sse2.packsswb.128", "avx2.packsswb", "avx512.packsswb.512")),
        (16, ("sse2.packuswb.128", "avx2.packuswb", "avx512.packuswb.512")),
        (32, ("sse2.packssdw.128", "avx2.packssdw", "avx512.packssdw.512")),
        (32, ("sse41.packusdw", "avx2.packusdw", "avx512.packusdw.512")),
    ):
        for name in forms("{}", names):
            a = (bits(name) // u, u)
            ops.append(Op(name, (2 * a[0], u // 2), (a, a), alive=True, folds=True))
    return ops


def signs() -> list[Op]:
    ops = []
    for w, letter in ((8, "b"), (16, "w"), (32, "d")):
        ops += lanewise(forms("{}", (f"ssse3.psign.{letter}.128", f"avx2.psign.{letter}")), w, alive=True)
    return ops


def high_products() -> list[Op]:
    return (
        lanewise(
            forms("{}", ("sse2.pmulh.w", "avx2.pmulh.w", "avx512.pmulh.w.512")), 16, alive=True, folds=True
        )
        + lanewise(
            forms("{}", ("sse2.pmulhu.w", "avx2.pmulhu.w", "avx512.pmulhu.w.512")), 16, alive=True, folds=True
        )
        + lanewise(
            forms("{}", ("ssse3.pmul.hr.sw.128", "avx2.pmul.hr.sw", "avx512.pmul.hr.sw.512")), 16, folds=True
        )
    )


def absolute_differences() -> list[Op]:
    ops = []
    for name in forms("{}", ("sse2.psad.bw", "avx2.psad.bw", "avx512.psad.bw.512")):
        a = (bits(name) // 8, 8)
        ops.append(Op(name, (a[0] // 8, 64), (a, a), alive=True))
    return ops


def neighbours() -> list[Op]:
    ops = []
    for step in ("phadd", "phsub"):
        for w, letter in ((16, "w"), (32, "d"), (16, "sw")):
            names = (f"ssse3.{step}.{letter}.128", f"avx2.{step}.{letter}")
            ops += lanewise(forms("{}", names), w, alive=True)
    return ops


def blends() -> list[Op]:
    # Alive2 knows the 256-bit form only.
    return lanewise(["llvm.x86.sse41.pblendvb"], 8, 3, folds=True) + lanewise(
        ["llvm.x86.avx2.pblendvb"], 8, 3, alive=True, folds=True
    )


def saturating_dot_products() -> list[Op]:
    ops = []
    for step, w in (("vpdpbusds", 8), ("vpdpwssd", 16), ("vpdpwssds", 16)):
        for width in (128, 256, 512):
            acc, b = (width // 32, 32), (width // w, w)
            ops.append(Op(f"llvm.x86.avx512.{step}.{width}", acc, (acc, b, b)))
    return ops


def masked_moves() -> list[Op]:
    """The down-converting moves with a mask, at each pair of lane widths and vector width the pin has."""
    ops = []
    widths = {"b": 8, "w": 16, "d": 32, "q": 64}
    for step in ("pmov", "pmovs", "pmovus"):
        for pair in ("db", "dw", "qb", "qd", "qw", "wb"):
            for size in (128, 256, 512):
                # Without saturation, clang lowers these four to a `trunc` and a `select`.
                if step == "pmov" and (pair, size) in (("qd", 256), ("qd", 512), ("wb", 256), ("wb", 512)):
                    continue
                u, w = widths[pair[0]], widths[pair[1]]
                m = size // u
                result = (max(m, 128 // w), w)
                name = f"llvm.x86.avx512.mask.{step}.{pair}.{size}"
                ops.append(Op(name, result, ((m, u), result, (0, max(8, m)))))
    return ops


def bit_fields() -> list[Op]:
    """BZHI and BEXTR, whose second operand is an index, or a start and a length, in its low bytes."""
    ops = []
    for step in ("bzhi", "bextr"):
        for w in (32, 64):
            ops.append(
                Op(f"llvm.x86.bmi.{step}.{w}", (0, w), ((0, w), (0, w)), picks=("", "field"), folds=True)
            )
    return ops


def checksums() -> list[Op]:
    ops = [Op(f"llvm.x86.sse42.crc32.32.{k}", (0, 32), ((0, 32), (0, k))) for k in (8, 16, 32)]
    return [*ops, Op("llvm.x86.sse42.crc32.64.64", (0, 64), ((0, 64), (0, 64)))]


def tests() -> list[Op]:
    ops = []
    for flag in ("ptestz", "ptestc", "ptestnzc"):
        ops.append(Op(f"llvm.x86.sse41.{flag}", (0, 32), ((2, 64), (2, 64))))
        ops.append(Op(f"llvm.x86.avx.{flag}.256", (0, 32), ((4, 64), (4, 64))))
    return ops


def least_word() -> list[Op]:
    return [Op("llvm.x86.sse41.phminposuw", (8, 16), ((8, 16),))]


def galois_field() -> list[Op]:
    """IRLean/X86Crypto.lean: GFNI. The affine maps with a few constants, the AES S-box's 0x63 among them."""
    ops = []
    for width in (128, 256, 512):
        a = (width // 8, 8)
        for step in ("vgf2p8affineqb", "vgf2p8affineinvqb"):
            ops += [
                Op(f"llvm.x86.{step}.{width}", a, (a, a), ("i8", imm), picks=("bytes",))
                for imm in (0, 0x63, 0xFF)
            ]
        ops.append(Op(f"llvm.x86.vgf2p8mulb.{width}", a, (a, a), picks=("bytes",)))
    return ops


OPS = dot_products() + bit_functions() + carry_less() + aes() + averages() + packs() + signs()
OPS += high_products() + absolute_differences() + saturating_dot_products() + neighbours() + blends()


def register_state() -> list[Op]:
    """VZEROUPPER, which the model ignores: 256-bit values computed before it and used after it have to come
    out the same. Native code is optimized here, so the values are in registers: with AVX2 alone, in ones the
    instruction zeroes half of, so LLVM saves them around it, and with AVX-512, in YMM16 and up, which it
    leaves alone. There's nothing in the model to get wrong, so no wrong version."""
    a = (4, 64)
    body = "%s = add <4 x i64> %a0, %a1\n  call void @llvm.x86.avx.vzeroupper()\n  %r = xor <4 x i64> %s, %a0"
    how: dict[str, Any] = {
        "body": body,
        "declares": "declare void @llvm.x86.avx.vzeroupper()",
        "mutant": False,
    }
    return [
        Op("llvm.x86.avx.vzeroupper", a, (a, a), optimized="+avx2", tag="_saved", **how),
        Op("llvm.x86.avx.vzeroupper", a, (a, a), optimized="+avx2,+avx512f,+avx512vl", tag="_kept", **how),
    ]


OPS += bit_fields() + masked_moves() + tests() + checksums() + least_word() + galois_field()
OPS += register_state()


def covered(ops: list[Op]) -> set[str]:
    return {op.intrinsic for op in ops}


def extremes(w: int) -> list[int]:
    m = (1 << w) - 1
    top = 1 << (w - 1)
    return sorted({0, 1, 2, m, m - 1, top, top - 1, (top + 1) & m})


def count(op: Op, w: int, rand: Any) -> int:
    """A shift's count, `w` bits of it, near where its rules change: below, at and past the lane width."""
    lw = op.args[0][1]
    return rand.choice([0, 1, 3, lw - 1, lw, lw + 1, rand.getrandbits(w), rand.randrange(64)]) % (1 << w)


def operand(op: Op, i: int, rand: Any, edge: bool = False) -> list[int]:
    """The lanes of operand `i`."""
    n, w = max(op.args[i][0], 1), op.args[i][1]
    if op.pick(i) == "count64":
        # The count is the low 64 bits, read from the first lanes, lowest first. The rest aren't read.
        c, per = count(op, 64, rand), 64 // w
        return [(c >> (w * j)) & ((1 << w) - 1) for j in range(per)] + [
            rand.getrandbits(w) for _ in range(n - per)
        ]
    if op.pick(i) == "count":
        return [count(op, w, rand) for _ in range(n)]
    if op.pick(i) == "field":
        # A start and a length near the width, in the low two bytes, with other bits set half the time.
        near = [0, 1, 7, w // 2, w - 1, w, w + 1, 255, rand.randrange(256)]
        high = rand.getrandbits(w - 16) << 16 if rand.random() < 0.5 else 0
        return [rand.choice(near) | rand.choice(near) << 8 | high for _ in range(n)]
    return [rand.choice(extremes(w)) if edge else rand.getrandbits(w) for _ in range(n)]


def value_cases(
    op: Op, rand: Any, random: int = 32, edges: int = 16, splats: int = 64, tables: bool = True
) -> list[list[list[int]]]:
    """Inputs with a value in every lane: random ones, ones at the extremes, and every operand a splat of an
    extreme, each against each, where saturation and wrapping show. Each is the lanes of each operand."""
    out = [[operand(op, i, rand) for i in range(len(op.args))] for _ in range(random)]
    out += [[operand(op, i, rand, True) for i in range(len(op.args))] for _ in range(edges)]
    product = list(itertools.product(*[extremes(w) for _, w in op.args]))
    for picked in product if len(product) <= splats else rand.sample(product, splats):
        out.append([[x] * max(n, 1) for x, (n, _) in zip(picked, op.args, strict=True)])
    for i, (n, w) in enumerate(op.args):
        if op.pick(i) == "bytes" and tables:
            # Every byte of this operand the same, for each value a byte has.
            for byte in range(256):
                case = [operand(op, j, rand) for j in range(len(op.args))]
                case[i] = [int.from_bytes(bytes([byte]) * (w // 8), "little")] * max(n, 1)
                out.append(case)
    return out


def poison_cases(op: Op, rand: Any, count: int = 8) -> list[list[list[int]]]:
    """Inputs with poison lanes: in one operand or in each, one lane or several."""
    out = []
    for k in range(count):
        case = [operand(op, i, rand, k % 3 == 2) for i in range(len(op.args))]
        for i, (n, _) in enumerate(op.args):
            if (k % 2 == 0 and i != (k // 2) % len(op.args)) or n == 0:
                continue
            for at in rand.sample(range(n), 1 if k < count // 2 else max(1, n // 4)):
                case[i][at] = POISON
        out.append(case)
    return out


def wrong_module(lean: str) -> str:
    """Emitted Lean with each call into `IRLean.X86` one to its wrong version, in a namespace of its own."""
    twin = re.sub(r"\bX86\.", "X86Wrong.", lean)
    twin = re.sub(r"^(namespace|end) Ops$", r"\1 OpsWrong", twin, flags=re.M)
    return twin.replace("import IRLean\n", "import IRLean\nimport X86Wrong\n", 1)
