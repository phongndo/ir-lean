#!/usr/bin/env python3
"""SEM-08: everything the pinned LLVM IR can contain, each item modeled, refused or assumed, and a check that
the emitter does what each item's class says.

The items come from the pinned source, read again on every check:

  intrinsic            every `Intrinsic` record in llvm/include/llvm/IR/Intrinsics*.td, through llvm-tblgen
  attribute            every attribute in llvm/include/llvm/IR/Attributes.td, at each place it can go: on a
                       function, a parameter or a return value, and the same three at a call
  string attribute     the string attributes Attributes.td defines, the ones the emitter allows, and any other
  metadata             every kind in llvm/include/llvm/IR/FixedMetadataKinds.def, and any other kind
  instruction          every opcode in llvm/include/llvm/IR/Instruction.def
  type                 every TypeID in llvm/include/llvm/IR/Type.h
  linkage              every LinkageTypes in llvm/include/llvm/IR/GlobalValue.h
  calling convention   every calling convention in llvm/include/llvm/IR/CallingConv.h
  constant             every HANDLE_CONSTANT and HANDLE_GLOBAL_VALUE in llvm/include/llvm/IR/Value.def
  operand bundle       every bundle tag LLVMContext knows, and each llvm.assume bundle in BundleAttributes.def
  form                 forms of these the emitter treats differently, such as `udiv` of vectors, listed here

Each item gets a class from the rules below, which name modeled and assumed items one by one. Only refused
items can be matched by a prefix, so nothing new is ever modeled or assumed by accident, and an item no rule
matches fails the check. A refused item another lane is working on names that lane.

usage:
  tests/ir_features.py generate [--tool T] [--probe P]   write tests/llvm_scope/ir-features.json
  tests/ir_features.py check --tool T --probe P [--no-lean]
  tests/ir_features.py summary                           the totals, from the file in the repo

`check` derives the items again and fails if the file differs, then builds a probe for each item, runs the
emitter on it, and fails if what the emitter does disagrees with the class: a modeled or assumed item has to
translate, and the Lean the emitter prints for it has to elaborate, and a refused item has to be refused.
`generate` and `check` need the dev shell, for $LLVM_PROJECT_SRC and llvm-tblgen. docs/ir-features.md says
what each class means.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import os
import re
import sys
import tempfile
from collections import Counter, defaultdict
from collections.abc import Callable
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
sys.path.append(str(ROOT / "tools"))
from irlean import lean, pins, proc, schemas  # noqa: E402

FILE = ROOT / "tests" / "llvm_scope" / "ir-features.json"
SCHEMA = schemas.IR_FEATURES
EMITTER = ROOT / "src" / "Emitter.cpp"
KINDS = (
    "instruction",
    "type",
    "intrinsic",
    "attribute",
    "string attribute",
    "metadata",
    "linkage",
    "calling convention",
    "constant",
    "operand bundle",
    "form",
)
CLASSES = {
    "modeled": "IRLean gives it LLVM's meaning, checked on each run or computed, as LangRef at the pin says",
    "assumed": "Translated, and the model ignores it: it only guides optimization, lowering or tools, or it "
    "can't "
    "be broken in the model. The reason says which",
    "refused": "The emitter refuses any function containing it, so no theorem is about one",
}
LANES = {
    "floating point": "SEM-05, running since 2026-11-09: floating-point types, operations, intrinsics, "
    "fast-math "
    "flags and floating-point attributes",
    "external calls and globals": "Running since 2026-11-09: calls to declarations, variadic calls, "
    "call-site "
    "attributes, external globals, constant expressions over them, and linkage",
    "memory": "F4, SEM-06, next in the semantics stream: refinement for functions with memory",
    "long tail": "This lane, since 2026-11-09: what the emitter refuses in LLVM's regression tests and no "
    "other "
    "lane covers",
}

# ------------------------------------------------------------------------------------------------------------
# Reasons. Each fixes a class, and for a refused item, the lane working on it, if any.


@dataclass(frozen=True)
class Reason:
    cls: str
    lane: str | None
    says: str


REASONS: dict[str, Reason] = {
    # Modeled.
    "integer": Reason(
        "modeled",
        None,
        "An integer operation in IRLean/Int.lean, checked by tests/opcheck.py "
        "against Alive2 and LLVM's constant folder",
    ),
    "vector": Reason(
        "modeled", None, "A vector of integers, lane by lane, in IRLean/Vec.lean and IRLean/Lanes.lean"
    ),
    "control": Reason(
        "modeled",
        None,
        "Control flow: IRLean's block driver runs blocks, phis are block "
        "arguments, and branching on poison is undefined",
    ),
    "call": Reason(
        "modeled",
        None,
        "A call to a function in the module that ir-lean translates, directly or through a pointer to one",
    ),
    "outside global": Reason(
        "modeled",
        None,
        "A global another module defines: an address, with no allocation in initial, so what it holds is the "
        "memory's (docs/calls.md)",
    ),
    "outside call": Reason(
        "modeled",
        None,
        "A call to a function the module only declares, answered by IRLean.World: an event in the run's "
        "trace, or for one without effects, an answer at the run's choice (docs/calls.md)",
    ),
    "aggregate": Reason("modeled", None, "A struct is a Lean tuple, field by field"),
    "float": Reason(
        "modeled",
        None,
        "Floating point in IRLean/Float.lean: a float is its bits, and each operation is checked by "
        "tests/fpcheck.py against LLVM's constant folder, the processor and Alive2 (SEM-05, docs/float.md)",
    ),
    "freeze": Reason(
        "modeled",
        None,
        "freeze of an integer: the value, or for poison a value the run chooses (F3, docs/refinement.md)",
    ),
    "memory": Reason(
        "modeled",
        None,
        "Memory, in IRLean/Mem.lean. A function that uses it takes and returns a "
        "Mem, and its Refines claim, in IRLean/MemRefine.lean, is for a target that "
        "allocates as its source does, until F4's stage 3",
    ),
    "x86 dot product": Reason(
        "modeled",
        None,
        "x86's integer dot products, in IRLean/X86.lean, checked against the processor by tests/x86native.py "
        "and tests/real/x86.ll, and against Alive2 and LLVM's constant folder by tests/x86check.py, where "
        "they know it",
    ),
    "x86 carry-less product": Reason(
        "modeled",
        None,
        "PCLMULQDQ, in IRLean/X86Crypto.lean, checked against the processor by tests/x86native.py. Neither "
        "Alive2 nor LLVM's constant folder computes it, and tests/x86check.py checks which quadwords poison "
        "reaches the result from against what InstCombine does",
    ),
    "x86 GFNI": Reason(
        "modeled",
        None,
        "GF2P8AFFINEQB, GF2P8AFFINEINVQB or GF2P8MULB, in IRLean/X86Crypto.lean, checked against the "
        "processor by tests/x86native.py, on every byte value. Neither Alive2 nor LLVM's constant folder "
        "computes it",
    ),
    "x86 register state": Reason(
        "modeled",
        None,
        "VZEROUPPER, which zeroes the upper halves of YMM0 to YMM15. No IR value is in one across it: LLVM "
        "gives the instruction those sixteen registers as definitions, so it changes no value, and the model "
        "does nothing. tests/x86native.py checks 256-bit values live across it on the processor, saved "
        "around it with AVX2 and kept in YMM16 and up with AVX-512",
    ),
    "x86 arithmetic": Reason(
        "modeled",
        None,
        "x86's integer arithmetic that isn't a generic operation lane by lane, in IRLean/X86Arith.lean, "
        "checked against the processor by tests/x86native.py, and against Alive2 and LLVM's constant folder "
        "by tests/x86check.py, where they know it",
    ),
    "x86 AES": Reason(
        "modeled",
        None,
        "An AES round, AESIMC or AESKEYGENASSIST, in IRLean/X86Crypto.lean, checked against the processor by "
        "tests/x86native.py, on every byte value. Neither Alive2 nor LLVM's constant folder computes it, so "
        "nothing but the model says what poison does to it",
    ),
    "value promise": Reason(
        "modeled",
        None,
        "A promise about a value, checked where the value is made: "
        "noundef is undefined on poison, and range, nonnull and align make it poison, as "
        "LangRef says",
    ),
    "memory promise": Reason(
        "modeled",
        None,
        "A promise about memory, checked by Mem on each access through tags "
        "on pointers and frames for calls (#19)",
    ),
    "progress": Reason(
        "modeled",
        None,
        "A promise to progress or to return. A run that breaks it is undefined, IRLean/Promise.lean (SEM-07)",
    ),
    "always holds": Reason(
        "modeled", None, "It always holds in the model, which has no unwinding, threads or synchronization"
    ),
    "call graph": Reason(
        "modeled",
        None,
        "The emitter refuses it where the call graph says it could be false, so "
        "it holds of every function translated",
    ),
    "assume": Reason(
        "modeled",
        None,
        "llvm.assume: undefined if its condition is false, and its nonnull, align and noundef bundles "
        "checked",
    ),
    "identity": Reason("modeled", None, "Returns its operand: llvm.expect's hint has no meaning for a run"),
    "no effect": Reason("modeled", None, "Does nothing, as LangRef says"),
    "float setting": Reason(
        "assumed",
        None,
        "A floating-point setting for the backend, which lets it treat the function's own floating-point "
        "operations more loosely than IEEE 754. A function with no floating-point value gives it nothing to "
        "act on, so the emitter accepts it there, and on a function outside the module, which is answered "
        "from the world whatever it does. It refuses it on a function with a floating-point value, and at a "
        "call",
    ),
    "linkage": Reason(
        "modeled",
        None,
        "A definition that is certainly the one that runs: external, internal or "
        "private, and not one another module could replace when it's loaded",
    ),
    "odr copy": Reason(
        "modeled",
        None,
        "A linkonce_odr or weak_odr definition translates as this translation's "
        "copy, so a theorem is about that copy. Calls to one are refused (docs/trust.md)",
    ),
    "constant": Reason(
        "modeled",
        None,
        "A constant the model has: an integer, poison, null, zero, or a vector or struct of them",
    ),
    "global": Reason("modeled", None, "A global this module defines, with its initial bytes, in Mem"),
    "alias": Reason(
        "modeled",
        None,
        "An alias the linker can't replace, read as what it names, which is how LLVM "
        "strips it: Value::stripAndAccumulateConstantOffsets looks through no interposable alias",
    ),
    # Assumed.
    "hint": Reason(
        "assumed",
        None,
        "Only changes how code is optimized, inlined, laid out or lowered, not what a run does",
    ),
    "abi": Reason("assumed", None, "Only says how a target passes the value, not what it is"),
    "calling convention": Reason(
        "assumed",
        None,
        "Only says how arguments and results are passed. The caller's "
        "and the callee's have to match, or LangRef makes the call undefined, and ir-lean "
        "refuses a call where they differ",
    ),
    "debug": Reason("assumed", None, "Debug information, which has no meaning for a run"),
    "profile": Reason(
        "assumed", None, "A profile, a branch weight or a hint for a tool, with no meaning for a run"
    ),
    "target setting": Reason(
        "assumed",
        None,
        "A setting for the backend, a sanitizer, a profile or a tool, with no meaning in LangRef for a run "
        "of this function",
    ),
    "symbol metadata": Reason(
        "assumed",
        None,
        "Metadata on a function or a global that names, types, groups or "
        "places it for the linker, CFI or tools. The emitter doesn't read metadata on "
        "functions or globals. None says what a run does, apart from absolute_symbol, which "
        "narrows where a symbol is: a theorem holds for every address the model allows, "
        "which includes those",
    ),
    "hardening": Reason(
        "assumed",
        None,
        "Hardening, instrumentation or patching that code generation or a later pass adds, such as a "
        "sanitizer or a shadow call stack. The IR the emitter reads is what runs, before any of it",
    ),
    "one thread": Reason(
        "assumed",
        None,
        "Says which transformations keep code right when many threads run it in step, as on a GPU. The model "
        "runs one thread, which none of these constrains",
    ),
    "no callback": Reason(
        "assumed",
        None,
        'LangRef: it "has no effect on functions defined in the current module". On a call the model answers '
        "from the world, the calls' own check refuses it, and a call that never returns stops the model",
    ),
    "speculatable": Reason(
        "assumed",
        None,
        "Promises the function has no effects and no undefined behavior. A run of the function itself is "
        "the same with it or without, so the emitter accepts it on a function without memory, and refuses it "
        "on one with memory, and every call to such a function, since LangRef makes a call undefined where "
        "the function would be, even when the call doesn't run",
    ),
    "noreturn": Reason(
        "modeled",
        None,
        'LangRef: it "produces undefined behavior at runtime if the function ever does dynamically return", '
        "so the emitter makes each return undefined",
    ),
    "string on a value": Reason(
        "assumed",
        None,
        "A string attribute on a parameter or a return value. LangRef "
        "gives string attributes no meaning; targets read them as settings",
    ),
    "tail call": Reason(
        "assumed",
        None,
        "tail and musttail also promise the callee doesn't touch the caller's "
        "allocas, which the model doesn't check. A function without memory has none, and for one "
        "with memory this is an assumption until F4",
    ),
    "upgraded debug": Reason(
        "assumed",
        None,
        "LLVM's IR reader turns calls to it into debug records, which the emitter doesn't read",
    ),
    "upgraded": Reason(
        "modeled",
        None,
        "LLVM's IR reader rewrites calls to it as instructions the model has, so "
        "the emitter never sees the intrinsic",
    ),
    "verifier": Reason(
        "assumed",
        None,
        "Only on an intrinsic's declaration, where it says an argument has to be a "
        "constant, which LLVM's verifier checks. Anywhere else the verifier rejects it",
    ),
    "intrinsic operand": Reason(
        "assumed", None, "Only an operand of an intrinsic, whose own class covers it"
    ),
    "x86 bit function": Reason(
        "modeled",
        None,
        "One of x86's pure bit functions, VPTERNLOG, PSHUFB and the shifts, in IRLean/X86Bits.lean, checked "
        "by tests/vecopcheck.py against Alive2, both ways, and LLVM's constant folder with x86's own folds, "
        "and by tests/x86native.py against the processor",
    ),
    "scalable vector": Reason(
        "modeled",
        None,
        "A scalable vector of integers, a Vec (vscale * N) M, with vscale a parameter every function in the "
        "module takes, in IRLean/Scalable.lean. Checked against the fixed-width forms and LLVM's constant "
        "folder by tests/scalablecheck.py, and decided in docs/scalable-vectors.md",
    ),
    "vscale range": Reason(
        "modeled",
        None,
        "A run with vscale outside the function's vscale_range is undefined, checked at its entry, "
        "IRLean/Scalable.lean",
    ),
    "data layout": Reason(
        "modeled",
        None,
        "A data layout that says what Mem assumes, read from it: 64-bit pointers in address space 0, all of "
        "them address, null all zeros, and little-endian",
    ),
    # Refused, with the lane working on it.
    "floating point": Reason("refused", "floating point", "Floating point"),
    "float shape": Reason(
        "refused",
        "floating point",
        "A conversion intrinsic whose result has another number of lanes than its argument, which LangRef "
        "rules out and LLVM's verifier allows",
    ),
    "external": Reason(
        "refused",
        "external calls and globals",
        "A call to a declaration, an external global, a call-site promise or a linkage the model can't trust",
    ),
    "objc": Reason(
        "refused",
        "external calls and globals",
        "The Objective-C runtime's functions, which are calls outside the module",
    ),
    "memory model": Reason(
        "refused",
        "memory",
        "Memory the model doesn't have yet: aliasing and invariance "
        "promises, masked and element-wise accesses, provenance casts, and object sizes",
    ),
    "scalable": Reason("refused", "long tail", "Scalable vectors, llvm.vscale and what depends on them"),
    "vector gap": Reason(
        "refused", "long tail", "A vector form or operation the emitter doesn't translate yet"
    ),
    "integer gap": Reason("refused", "long tail", "An integer operation the model doesn't have yet"),
    "x86": Reason(
        "refused",
        "long tail",
        "An x86 intrinsic the model doesn't have. It stays refused, by name, until it's modeled and checked "
        "against the processor, and against Alive2 and LLVM's constant folder where they know it. "
        "docs/x86-intrinsics.md ranks them",
    ),
    "layout": Reason(
        "refused",
        "memory",
        "Pointers Mem doesn't have yet: in another address space, in a vector, or, in a function with "
        "memory, narrower than 64 bits, with fewer address bits, or with a null that isn't all zeros",
    ),
    "big-endian": Reason(
        "refused",
        "long tail",
        "A bitcast between integers and vectors in a big-endian module, whose lane order the model "
        "doesn't have",
    ),
    "exceptions": Reason(
        "refused",
        "long tail",
        "Exception handling: invoke, landingpad, resume and the funclet instructions. Refused on review: a "
        "landing pad's value is a pointer to the exception and a selector the personality function, outside "
        "the module, chooses, so it waits on memory and on calls. docs/ir-features.md",
    ),
    "aggregate gap": Reason("refused", "long tail", "An aggregate form the emitter doesn't translate yet"),
    "calling convention mismatch": Reason(
        "refused",
        "long tail",
        "A call whose calling convention or ABI attributes, such as inreg or signext, aren't the callee's, "
        "which LangRef makes undefined, refused until modeled so",
    ),
    "attribute review": Reason(
        "refused",
        "long tail",
        "An attribute the long tail is reviewing, to accept "
        "where it has no effect on a function without memory",
    ),
    "metadata review": Reason(
        "refused",
        "long tail",
        "Metadata the long tail is reviewing, to accept where it has no meaning for a run, or model",
    ),
    "nondeterministic": Reason(
        "refused",
        "long tail",
        "An intrinsic whose result the compiler chooses, such as "
        "llvm.is.constant, to model as a choice through IRLean.Choice",
    ),
    "identity gap": Reason(
        "refused", "long tail", "An intrinsic that returns its operand or does nothing, to model"
    ),
    "trap": Reason("refused", "long tail", "A trap, to model as a stop"),
    # Refused, with no lane on it.
    "undef": Reason(
        "refused", None, "undef stays out of the model, by the maintainer's decision of 2026-11-09"
    ),
    "concurrency": Reason(
        "refused", None, "Atomics, fences and volatile accesses, SEM-09, which waits on F4"
    ),
    "other target": Reason("refused", None, "Another target's intrinsic, which nothing in the model covers"),
    "coroutines": Reason("refused", None, "Coroutines, which nothing in the model covers"),
    "gc": Reason("refused", None, "Garbage collection and statepoints, which nothing in the model covers"),
    "instrumentation": Reason(
        "refused", None, "Sanitizer and profiling instrumentation, which nothing in the model covers"
    ),
    "machine": Reason(
        "refused",
        None,
        "Machine state: frame and return addresses, registers, counters, stack "
        "saves, trampolines, hardware loops and caches",
    ),
    "asm": Reason("refused", None, "Inline assembly, which nothing in the model covers"),
    "convergence": Reason(
        "refused", None, "GPU convergence control and tokens, which nothing in the model covers"
    ),
    "pointer authentication": Reason(
        "refused", None, "Pointer authentication, which nothing in the model covers"
    ),
    "cfi": Reason("refused", None, "Control-flow integrity checks, which nothing in the model covers"),
    "deoptimization": Reason(
        "refused",
        None,
        "Deoptimization, guards, patchpoints and stack maps, which nothing in the model covers",
    ),
    "token": Reason("refused", None, "Tokens, which only the constructs above make"),
    "variadic": Reason(
        "refused",
        None,
        "Variadic functions: their definitions, va_arg and the va_ intrinsics, "
        "which nothing in the model covers. Calls to variadic declarations are the external calls "
        "lane's",
    ),
    "progress effect": Reason(
        "refused",
        None,
        "llvm.sideeffect, which LangRef makes observable progress, and the "
        "model has no observable effects, so a loop calling it would be undefined under a "
        "promise",
    ),
    "not in IR": Reason(
        "refused",
        None,
        "Can't be written in IR at the pin: it's internal to LLVM's passes or "
        "gone from the IR format, so the emitter never sees it",
    ),
    "promise": Reason("refused", None, "A promise the model doesn't check, and no lane plans to"),
    "not planned": Reason("refused", None, "Nothing in the model covers it, and no lane plans to"),
}

# ------------------------------------------------------------------------------------------------------------
# Rules. An item is matched by a rule naming it exactly, or failing that, by one with a prefix of its name. A
# modeled or assumed rule names its items exactly. An item matched by two exact rules, or by no exact rule and
# two prefixes, or by nothing, fails.


@dataclass
class Rule:
    reason: str
    names: frozenset[str] = frozenset()
    prefixes: tuple[str, ...] = ()
    at: frozenset[str] = frozenset()  # attribute positions, or all if empty


def R(reason: str, names: str = "", prefixes: str = "", at: str = "") -> Rule:
    return Rule(
        reason,
        frozenset(names.split()),
        tuple(prefixes.split()),
        frozenset(p.strip() for p in at.split(",") if p.strip()),
    )


# The generic intrinsics, by family. Every one at the pin is here, by name, apart from four whole families
# matched by prefix, all refused.
INTRINSIC_RULES = [
    R(
        "integer",
        "llvm.abs llvm.bitreverse llvm.bswap llvm.ctlz llvm.ctpop llvm.cttz llvm.fshl llvm.fshr "
        "llvm.sadd.sat "
        "llvm.sadd.with.overflow llvm.scmp llvm.smax llvm.smin llvm.smul.with.overflow llvm.ssub.sat "
        "llvm.ssub.with.overflow llvm.uadd.sat llvm.uadd.with.overflow llvm.ucmp llvm.umax llvm.umin "
        "llvm.umul.with.overflow llvm.usub.sat llvm.usub.with.overflow",
    ),
    R(
        "vector",
        "llvm.vector.reduce.add llvm.vector.reduce.and llvm.vector.reduce.mul llvm.vector.reduce.or "
        "llvm.vector.reduce.smax llvm.vector.reduce.smin llvm.vector.reduce.umax llvm.vector.reduce.umin "
        "llvm.vector.reduce.xor",
    ),
    R("assume", "llvm.assume"),
    R(
        "scalable vector",
        "llvm.vscale llvm.stepvector llvm.vector.reverse llvm.vector.insert llvm.vector.extract",
    ),
    R("identity", "llvm.expect"),
    R("no effect", "llvm.donothing llvm.prefetch"),
    R("memory", "llvm.memcpy llvm.memmove llvm.memset llvm.lifetime.start llvm.lifetime.end"),
    R(
        "x86 dot product",
        "llvm.x86.ssse3.pmadd.ub.sw.128 llvm.x86.avx2.pmadd.ub.sw llvm.x86.avx512.pmaddubs.w.512 "
        "llvm.x86.sse2.pmadd.wd llvm.x86.avx2.pmadd.wd llvm.x86.avx512.pmaddw.d.512 "
        "llvm.x86.avx512.vpdpbusd.128 "
        "llvm.x86.avx512.vpdpbusd.256 llvm.x86.avx512.vpdpbusd.512",
    ),
    R("x86 carry-less product", "llvm.x86.pclmulqdq llvm.x86.pclmulqdq.256 llvm.x86.pclmulqdq.512"),
    R(
        "x86 arithmetic",
        "llvm.x86.sse2.pavg.b llvm.x86.sse2.pavg.w llvm.x86.avx2.pavg.b llvm.x86.avx2.pavg.w "
        "llvm.x86.avx512.pavg.b.512 llvm.x86.avx512.pavg.w.512 "
        "llvm.x86.sse2.packsswb.128 llvm.x86.avx2.packsswb llvm.x86.avx512.packsswb.512 "
        "llvm.x86.sse2.packuswb.128 llvm.x86.avx2.packuswb llvm.x86.avx512.packuswb.512 "
        "llvm.x86.sse2.packssdw.128 llvm.x86.avx2.packssdw llvm.x86.avx512.packssdw.512 "
        "llvm.x86.sse41.packusdw llvm.x86.avx2.packusdw llvm.x86.avx512.packusdw.512 "
        "llvm.x86.ssse3.psign.b.128 llvm.x86.ssse3.psign.w.128 llvm.x86.ssse3.psign.d.128 "
        "llvm.x86.avx2.psign.b llvm.x86.avx2.psign.w llvm.x86.avx2.psign.d "
        "llvm.x86.sse2.pmulh.w llvm.x86.avx2.pmulh.w llvm.x86.avx512.pmulh.w.512 "
        "llvm.x86.sse2.pmulhu.w llvm.x86.avx2.pmulhu.w llvm.x86.avx512.pmulhu.w.512 "
        "llvm.x86.ssse3.pmul.hr.sw.128 llvm.x86.avx2.pmul.hr.sw llvm.x86.avx512.pmul.hr.sw.512 "
        "llvm.x86.sse2.psad.bw llvm.x86.avx2.psad.bw llvm.x86.avx512.psad.bw.512 "
        "llvm.x86.avx512.vpdpbusds.128 llvm.x86.avx512.vpdpbusds.256 llvm.x86.avx512.vpdpbusds.512 "
        "llvm.x86.avx512.vpdpwssd.128 llvm.x86.avx512.vpdpwssd.256 llvm.x86.avx512.vpdpwssd.512 "
        "llvm.x86.avx512.vpdpwssds.128 llvm.x86.avx512.vpdpwssds.256 llvm.x86.avx512.vpdpwssds.512 "
        "llvm.x86.ssse3.phadd.w.128 llvm.x86.ssse3.phadd.d.128 llvm.x86.ssse3.phadd.sw.128 "
        "llvm.x86.avx2.phadd.w llvm.x86.avx2.phadd.d llvm.x86.avx2.phadd.sw "
        "llvm.x86.ssse3.phsub.w.128 llvm.x86.ssse3.phsub.d.128 llvm.x86.ssse3.phsub.sw.128 "
        "llvm.x86.avx2.phsub.w llvm.x86.avx2.phsub.d llvm.x86.avx2.phsub.sw "
        "llvm.x86.sse41.pblendvb llvm.x86.avx2.pblendvb "
        "llvm.x86.bmi.bzhi.32 llvm.x86.bmi.bzhi.64 llvm.x86.bmi.bextr.32 llvm.x86.bmi.bextr.64 "
        "llvm.x86.sse41.ptestz llvm.x86.sse41.ptestc llvm.x86.sse41.ptestnzc "
        "llvm.x86.avx.ptestz.256 llvm.x86.avx.ptestc.256 llvm.x86.avx.ptestnzc.256 "
        "llvm.x86.sse42.crc32.32.8 llvm.x86.sse42.crc32.32.16 llvm.x86.sse42.crc32.32.32 "
        "llvm.x86.sse42.crc32.64.64 llvm.x86.sse41.phminposuw "
        "llvm.x86.avx512.mask.pmov.db.128 llvm.x86.avx512.mask.pmov.db.256 "
        "llvm.x86.avx512.mask.pmov.db.512 llvm.x86.avx512.mask.pmov.dw.128 "
        "llvm.x86.avx512.mask.pmov.dw.256 llvm.x86.avx512.mask.pmov.dw.512 "
        "llvm.x86.avx512.mask.pmov.qb.128 llvm.x86.avx512.mask.pmov.qb.256 "
        "llvm.x86.avx512.mask.pmov.qb.512 llvm.x86.avx512.mask.pmov.qd.128 "
        "llvm.x86.avx512.mask.pmov.qw.128 llvm.x86.avx512.mask.pmov.qw.256 "
        "llvm.x86.avx512.mask.pmov.qw.512 llvm.x86.avx512.mask.pmov.wb.128 "
        "llvm.x86.avx512.mask.pmovs.db.128 llvm.x86.avx512.mask.pmovs.db.256 "
        "llvm.x86.avx512.mask.pmovs.db.512 llvm.x86.avx512.mask.pmovs.dw.128 "
        "llvm.x86.avx512.mask.pmovs.dw.256 llvm.x86.avx512.mask.pmovs.dw.512 "
        "llvm.x86.avx512.mask.pmovs.qb.128 llvm.x86.avx512.mask.pmovs.qb.256 "
        "llvm.x86.avx512.mask.pmovs.qb.512 llvm.x86.avx512.mask.pmovs.qd.128 "
        "llvm.x86.avx512.mask.pmovs.qd.256 llvm.x86.avx512.mask.pmovs.qd.512 "
        "llvm.x86.avx512.mask.pmovs.qw.128 llvm.x86.avx512.mask.pmovs.qw.256 "
        "llvm.x86.avx512.mask.pmovs.qw.512 llvm.x86.avx512.mask.pmovs.wb.128 "
        "llvm.x86.avx512.mask.pmovs.wb.256 llvm.x86.avx512.mask.pmovs.wb.512 "
        "llvm.x86.avx512.mask.pmovus.db.128 llvm.x86.avx512.mask.pmovus.db.256 "
        "llvm.x86.avx512.mask.pmovus.db.512 llvm.x86.avx512.mask.pmovus.dw.128 "
        "llvm.x86.avx512.mask.pmovus.dw.256 llvm.x86.avx512.mask.pmovus.dw.512 "
        "llvm.x86.avx512.mask.pmovus.qb.128 llvm.x86.avx512.mask.pmovus.qb.256 "
        "llvm.x86.avx512.mask.pmovus.qb.512 llvm.x86.avx512.mask.pmovus.qd.128 "
        "llvm.x86.avx512.mask.pmovus.qd.256 llvm.x86.avx512.mask.pmovus.qd.512 "
        "llvm.x86.avx512.mask.pmovus.qw.128 llvm.x86.avx512.mask.pmovus.qw.256 "
        "llvm.x86.avx512.mask.pmovus.qw.512 llvm.x86.avx512.mask.pmovus.wb.128 "
        "llvm.x86.avx512.mask.pmovus.wb.256 llvm.x86.avx512.mask.pmovus.wb.512",
    ),
    R("x86 register state", "llvm.x86.avx.vzeroupper"),
    R(
        "x86 GFNI",
        "llvm.x86.vgf2p8affineqb.128 llvm.x86.vgf2p8affineqb.256 llvm.x86.vgf2p8affineqb.512 "
        "llvm.x86.vgf2p8affineinvqb.128 llvm.x86.vgf2p8affineinvqb.256 llvm.x86.vgf2p8affineinvqb.512 "
        "llvm.x86.vgf2p8mulb.128 llvm.x86.vgf2p8mulb.256 llvm.x86.vgf2p8mulb.512",
    ),
    R(
        "x86 AES",
        "llvm.x86.aesni.aesenc llvm.x86.aesni.aesenc.256 llvm.x86.aesni.aesenc.512 "
        "llvm.x86.aesni.aesenclast llvm.x86.aesni.aesenclast.256 llvm.x86.aesni.aesenclast.512 "
        "llvm.x86.aesni.aesdec llvm.x86.aesni.aesdec.256 llvm.x86.aesni.aesdec.512 "
        "llvm.x86.aesni.aesdeclast llvm.x86.aesni.aesdeclast.256 llvm.x86.aesni.aesdeclast.512 "
        "llvm.x86.aesni.aesimc llvm.x86.aesni.aeskeygenassist",
    ),
    R("upgraded debug", "llvm.dbg.assign llvm.dbg.declare llvm.dbg.label llvm.dbg.value"),
    R(
        "upgraded",
        "llvm.x86.avx512.broadcastmb.128 llvm.x86.avx512.broadcastmb.256 llvm.x86.avx512.broadcastmb.512 "
        "llvm.x86.avx512.broadcastmw.128 llvm.x86.avx512.broadcastmw.256 llvm.x86.avx512.broadcastmw.512",
    ),
    R("progress effect", "llvm.sideeffect"),
    R("float", "llvm.copysign llvm.fabs llvm.is.fpclass llvm.fptosi.sat llvm.fptoui.sat"),
    R(
        "floating point",
        "llvm.acos llvm.asin llvm.atan llvm.atan2 llvm.arithmetic.fence llvm.canonicalize llvm.ceil "
        "llvm.convert.from.arbitrary.fp llvm.convert.to.arbitrary.fp llvm.cos llvm.cosh "
        "llvm.exp "
        "llvm.exp10 llvm.exp2 llvm.floor llvm.fma llvm.fmuladd "
        "llvm.fptrunc.round llvm.frexp llvm.get.fpenv llvm.get.fpmode llvm.get.rounding "
        "llvm.ldexp llvm.llrint llvm.llround llvm.log llvm.log10 llvm.log2 llvm.lrint llvm.lround "
        "llvm.maximum "
        "llvm.maximumnum llvm.maxnum llvm.minimum llvm.minimumnum llvm.minnum llvm.modf llvm.nearbyint "
        "llvm.pow "
        "llvm.powi llvm.reset.fpenv llvm.reset.fpmode llvm.rint llvm.round llvm.roundeven llvm.set.fpenv "
        "llvm.set.fpmode llvm.set.rounding llvm.sin llvm.sincos llvm.sincospi llvm.sinh llvm.sqrt llvm.tan "
        "llvm.tanh llvm.trunc llvm.vector.partial.reduce.fadd llvm.vector.reduce.fadd "
        "llvm.vector.reduce.fmax "
        "llvm.vector.reduce.fmaximum llvm.vector.reduce.fmin llvm.vector.reduce.fminimum "
        "llvm.vector.reduce.fmul",
        "llvm.experimental.constrained.",
    ),
    R(
        "memory model",
        "llvm.memcpy.inline llvm.memset.inline llvm.memcpy.element.unordered.atomic "
        "llvm.memmove.element.unordered.atomic llvm.memset.element.unordered.atomic "
        "llvm.experimental.memset.pattern "
        "llvm.masked.load llvm.masked.store llvm.masked.gather llvm.masked.scatter llvm.masked.expandload "
        "llvm.masked.compressstore llvm.matrix.column.major.load llvm.matrix.column.major.store "
        "llvm.objectsize "
        "llvm.ptrmask llvm.invariant.start llvm.invariant.end llvm.launder.invariant.group "
        "llvm.strip.invariant.group llvm.load.relative llvm.experimental.vector.histogram.add "
        "llvm.experimental.vector.histogram.uadd.sat llvm.experimental.vector.histogram.umax "
        "llvm.experimental.vector.histogram.umin llvm.threadlocal.address "
        "llvm.experimental.noalias.scope.decl "
        "llvm.ptr.annotation llvm.var.annotation llvm.protected.field.ptr llvm.structured.alloca "
        "llvm.structured.gep "
        "llvm.preserve.array.access.index llvm.preserve.static.offset llvm.preserve.struct.access.index "
        "llvm.preserve.union.access.index llvm.call.preallocated.arg llvm.call.preallocated.setup "
        "llvm.call.preallocated.teardown",
    ),
    R(
        "scalable",
        "llvm.get.active.lane.mask llvm.experimental.get.vector.length "
        "llvm.experimental.cttz.elts llvm.loop.dependence.raw.mask llvm.loop.dependence.war.mask",
        "llvm.vp. llvm.experimental.vp.",
    ),
    R(
        "vector gap",
        "llvm.vector.splice.left "
        "llvm.vector.splice.right llvm.vector.partial.reduce.add llvm.experimental.vector.compress "
        "llvm.experimental.vector.match llvm.experimental.vector.extract.last.active llvm.masked.sdiv "
        "llvm.masked.srem llvm.masked.udiv llvm.masked.urem llvm.matrix.multiply llvm.matrix.transpose "
        "llvm.vector.interleave2 llvm.vector.interleave3 llvm.vector.interleave4 llvm.vector.interleave5 "
        "llvm.vector.interleave6 llvm.vector.interleave7 llvm.vector.interleave8 llvm.vector.deinterleave2 "
        "llvm.vector.deinterleave3 llvm.vector.deinterleave4 llvm.vector.deinterleave5 "
        "llvm.vector.deinterleave6 "
        "llvm.vector.deinterleave7 llvm.vector.deinterleave8",
    ),
    R(
        "integer gap",
        "llvm.clmul llvm.pdep llvm.pext llvm.sdiv.fix llvm.sdiv.fix.sat llvm.udiv.fix llvm.udiv.fix.sat "
        "llvm.smul.fix llvm.smul.fix.sat llvm.umul.fix llvm.umul.fix.sat llvm.sshl.sat llvm.ushl.sat",
    ),
    R(
        "nondeterministic",
        "llvm.is.constant llvm.allow.runtime.check llvm.allow.ubsan.check llvm.allow.sanitize.address "
        "llvm.allow.sanitize.hwaddress llvm.allow.sanitize.memory llvm.allow.sanitize.thread",
    ),
    R(
        "identity gap",
        "llvm.ssa.copy llvm.expect.with.probability llvm.annotation llvm.fake.use llvm.pseudoprobe "
        "llvm.codeview.annotation llvm.reloc.none llvm.cond.loop",
    ),
    R("trap", "llvm.trap llvm.debugtrap llvm.ubsantrap llvm.looptrap"),
    R("exceptions", "llvm.callbr.landingpad", "llvm.eh. llvm.seh."),
    R(
        "machine",
        "llvm.addressofreturnaddress llvm.frameaddress llvm.returnaddress llvm.sponentry llvm.stackaddress "
        "llvm.stackguard llvm.stackprotector llvm.stacksave llvm.stackrestore llvm.get.dynamic.area.offset "
        "llvm.localaddress llvm.localescape llvm.localrecover llvm.read_register llvm.read_volatile_register "
        "llvm.write_register llvm.write_volatile_register llvm.readcyclecounter llvm.readsteadycounter "
        "llvm.thread.pointer llvm.init.trampoline llvm.adjust.trampoline llvm.clear_cache "
        "llvm.pcmarker llvm.set.loop.iterations llvm.start.loop.iterations llvm.test.set.loop.iterations "
        "llvm.test.start.loop.iterations llvm.loop.decrement llvm.loop.decrement.reg "
        "llvm.swift.async.context.addr",
    ),
    R("variadic", "llvm.va_start llvm.va_end llvm.va_copy"),
    R(
        "instrumentation",
        "llvm.asan.check.memaccess llvm.alloc.token.id",
        "llvm.instrprof. llvm.xray. llvm.hwasan.",
    ),
    R("coroutines", "", "llvm.coro."),
    R("gc", "llvm.gcread llvm.gcroot llvm.gcwrite", "llvm.experimental.gc."),
    R("convergence", "", "llvm.experimental.convergence."),
    R("pointer authentication", "", "llvm.ptrauth."),
    R(
        "cfi",
        "llvm.type.test llvm.public.type.test llvm.type.checked.load llvm.type.checked.load.relative "
        "llvm.icall.branch.funnel",
    ),
    R(
        "deoptimization",
        "llvm.experimental.deoptimize llvm.experimental.guard llvm.experimental.widenable.condition "
        "llvm.experimental.patchpoint llvm.experimental.patchpoint.void llvm.experimental.stackmap",
    ),
    R("objc", "", "llvm.objc."),
    R(
        "x86 bit function",
        "llvm.x86.avx2.pshuf.b llvm.x86.avx2.psll.d llvm.x86.avx2.psll.q llvm.x86.avx2.psll.w "
        "llvm.x86.avx2.pslli.d llvm.x86.avx2.pslli.q llvm.x86.avx2.pslli.w llvm.x86.avx2.psllv.d "
        "llvm.x86.avx2.psllv.d.256 llvm.x86.avx2.psllv.q llvm.x86.avx2.psllv.q.256 llvm.x86.avx2.psra.d "
        "llvm.x86.avx2.psra.w llvm.x86.avx2.psrai.d llvm.x86.avx2.psrai.w llvm.x86.avx2.psrav.d "
        "llvm.x86.avx2.psrav.d.256 llvm.x86.avx2.psrl.d llvm.x86.avx2.psrl.q llvm.x86.avx2.psrl.w "
        "llvm.x86.avx2.psrli.d llvm.x86.avx2.psrli.q llvm.x86.avx2.psrli.w llvm.x86.avx2.psrlv.d "
        "llvm.x86.avx2.psrlv.d.256 llvm.x86.avx2.psrlv.q llvm.x86.avx2.psrlv.q.256 "
        "llvm.x86.avx512.pshuf.b.512 llvm.x86.avx512.psll.d.512 llvm.x86.avx512.psll.q.512 "
        "llvm.x86.avx512.psll.w.512 llvm.x86.avx512.pslli.d.512 llvm.x86.avx512.pslli.q.512 "
        "llvm.x86.avx512.pslli.w.512 llvm.x86.avx512.psllv.d.512 llvm.x86.avx512.psllv.q.512 "
        "llvm.x86.avx512.psllv.w.128 llvm.x86.avx512.psllv.w.256 llvm.x86.avx512.psllv.w.512 "
        "llvm.x86.avx512.psra.d.512 llvm.x86.avx512.psra.q.128 llvm.x86.avx512.psra.q.256 "
        "llvm.x86.avx512.psra.q.512 llvm.x86.avx512.psra.w.512 llvm.x86.avx512.psrai.d.512 "
        "llvm.x86.avx512.psrai.q.128 llvm.x86.avx512.psrai.q.256 llvm.x86.avx512.psrai.q.512 "
        "llvm.x86.avx512.psrai.w.512 llvm.x86.avx512.psrav.d.512 llvm.x86.avx512.psrav.q.128 "
        "llvm.x86.avx512.psrav.q.256 llvm.x86.avx512.psrav.q.512 llvm.x86.avx512.psrav.w.128 "
        "llvm.x86.avx512.psrav.w.256 llvm.x86.avx512.psrav.w.512 llvm.x86.avx512.psrl.d.512 "
        "llvm.x86.avx512.psrl.q.512 llvm.x86.avx512.psrl.w.512 llvm.x86.avx512.psrli.d.512 "
        "llvm.x86.avx512.psrli.q.512 llvm.x86.avx512.psrli.w.512 llvm.x86.avx512.psrlv.d.512 "
        "llvm.x86.avx512.psrlv.q.512 llvm.x86.avx512.psrlv.w.128 llvm.x86.avx512.psrlv.w.256 "
        "llvm.x86.avx512.psrlv.w.512 llvm.x86.avx512.pternlog.d.128 llvm.x86.avx512.pternlog.d.256 "
        "llvm.x86.avx512.pternlog.d.512 llvm.x86.avx512.pternlog.q.128 llvm.x86.avx512.pternlog.q.256 "
        "llvm.x86.avx512.pternlog.q.512 llvm.x86.sse2.psll.d llvm.x86.sse2.psll.q llvm.x86.sse2.psll.w "
        "llvm.x86.sse2.pslli.d llvm.x86.sse2.pslli.q llvm.x86.sse2.pslli.w llvm.x86.sse2.psra.d "
        "llvm.x86.sse2.psra.w llvm.x86.sse2.psrai.d llvm.x86.sse2.psrai.w llvm.x86.sse2.psrl.d "
        "llvm.x86.sse2.psrl.q llvm.x86.sse2.psrl.w llvm.x86.sse2.psrli.d llvm.x86.sse2.psrli.q "
        "llvm.x86.sse2.psrli.w llvm.x86.ssse3.pshuf.b.128",
    ),
    R("x86", "", "llvm.x86."),
    R(
        "other target",
        "",
        "llvm.aarch64. llvm.amdgcn. llvm.arm. llvm.avr. llvm.bpf. llvm.dx. llvm.hexagon. llvm.loongarch. "
        "llvm.mips. llvm.nvvm. llvm.ppc. llvm.r600. llvm.riscv. llvm.s390. llvm.spv. llvm.ve. llvm.wasm. "
        "llvm.xcore.",
    ),
]

# Attributes, by position. checkFunctionAttributes and checkValueAttributes in src/Emitter.cpp are what these
# describe.
DEF = "function"
VALUE = "parameter, return, call parameter, call return"
ATTRIBUTE_RULES = [
    R(
        "hint",
        "alwaysinline cold hot inlinehint minsize noinline nomerge nobuiltin noredzone optsize optnone ssp "
        "sspreq "
        "sspstrong uwtable",
        at="function, call",
    ),
    R("always holds", "nosync nounwind", at="function, call"),
    R("memory promise", "memory", at="function"),
    R("call graph", "nofree norecurse", at="function"),
    R("progress", "mustprogress willreturn", at="function"),
    R("external", "memory nofree norecurse mustprogress willreturn", at="call"),
    R("value promise", "noundef range nonnull align dereferenceable", at=VALUE),
    R("abi", "signext zeroext", at=VALUE),
    R("memory promise", "readonly writeonly readnone nofree initializes captures returned", at="parameter"),
    R("external", "readonly writeonly readnone nofree initializes captures returned", at="call parameter"),
    R("memory promise", "noalias", at="return"),
    R("external", "noalias", at="call return"),
    R("memory model", "noalias", at="parameter, call parameter"),
    R("float", "nofpclass", at=VALUE),
    R("floating point", "denormal_fpenv strictfp noimplicitfloat"),
    R("vscale range", "vscale_range", at="function"),
    R("scalable", "vscale_range", at="call"),
    R(
        "memory model",
        "byval byref inalloca preallocated sret elementtype writable dead_on_unwind dead_on_return "
        "dereferenceable_or_null allocalign allocptr allockind allocsize nest swifterror swiftself "
        "swiftasync "
        "null_pointer_is_valid",
    ),
    R("coroutines", "coro_only_destroy_when_complete coro_elide_safe presplitcoroutine"),
    R(
        "hardening",
        "sanitize_address sanitize_alloc_token sanitize_hwaddress sanitize_memtag sanitize_memory "
        "sanitize_numerical_stability sanitize_realtime sanitize_realtime_blocking sanitize_thread "
        "sanitize_type disable_sanitizer_instrumentation nosanitize_bounds nosanitize_coverage noprofile "
        "skipprofile optforfuzzing nocf_check fn_ret_thunk_extern hybrid_patchable shadowcallstack safestack "
        "speculative_load_hardening",
        at="function, call",
    ),
    R("hint", "flatten nooutline optdebug nonlazybind alignstack", at="function, call"),
    R("hint", "noipa", at="call"),
    # LLVM counts a `noipa` definition as one another module could replace, so the emitter refuses it with the
    # rest, through `isInterposable()`.
    R("external", "noipa", at="function"),
    R("one thread", "convergent noduplicate nodivergencesource", at="function, call"),
    R("no callback", "nocallback", at="function, call"),
    R("abi", "inreg noext alignstack", at=VALUE),
    R("noreturn", "noreturn", at="function"),
    R(
        "attribute review",
        "nocreateundeforpoison jumptable naked builtin returns_twice",
        at="function, call",
    ),
    R("speculatable", "speculatable", at="function"),
    R("attribute review", "speculatable", at="call"),
    R("attribute review", "noreturn", at="call"),
    R("verifier", "immarg"),
]

STRING_ATTRIBUTE_RULES = [
    R(
        "target setting",
        "alloc-family frame-pointer min-legal-vector-width no-builtins no-trapping-math probe-stack "
        "stack-protector-buffer-size target-cpu target-features tune-cpu zero-call-used-regs",
        at="function, call",
    ),
    R("string on a value", "any", at="parameter, return, call parameter, call return"),
    R("float setting", "less-precise-fpmad no-signed-zeros-fp-math", at="function"),
    R("floating point", "less-precise-fpmad no-signed-zeros-fp-math", at="call"),
    R(
        "target setting",
        "no-jump-tables no-inline-line-tables profile-sample-accurate use-sample-profile "
        "allow_direct_access_in_hot_patch_function marked_for_windows_hot_patching "
        "instcombine-no-verify-fixpoint",
        at="function, call",
    ),
    R("external", "loader-replaceable", at="function, call"),
    R("attribute review", "any", at="function, call"),
]
# Metadata kinds the emitter allows that FixedMetadataKinds.def doesn't fix: clang names them by string.
EMITTER_METADATA = ("heapallocsite", "srcloc")
# The string attributes the emitter allows on a function or a call, which aren't in Attributes.td.
ALLOWED_STRINGS = (
    "alloc-family frame-pointer min-legal-vector-width no-builtins no-trapping-math probe-stack "
    "stack-protector-buffer-size target-cpu target-features tune-cpu zero-call-used-regs "
    "instcombine-no-verify-fixpoint".split()
)

METADATA_RULES = [
    R("debug", "dbg"),
    R("progress", "llvm.loop"),
    R("value promise", "noundef"),
    R("profile", "prof unpredictable annotation nosanitize inline_history heapallocsite"),
    R("debug", "srcloc"),
    R(
        "symbol metadata",
        "type section_prefix associated vcall_visibility func_sanitize exclude kcfi_type implicit.ref "
        "elf_section_properties guid callback absolute_symbol",
    ),
    R(
        "memory model",
        "tbaa tbaa.struct invariant.load alias.scope noalias nontemporal llvm.mem.parallel_loop_access "
        "nonnull "
        "dereferenceable dereferenceable_or_null invariant.group align llvm.access.group noalias.addrspace "
        "nofree captures mem.cache_hint",
    ),
    R("floating point", "fpmath nofpclass"),
    R("external", "callees"),
    R("concurrency", "mmra"),
    R("coroutines", "coro.outside.frame"),
    R("not planned", "llvm.preserve.access.index"),
    R(
        "metadata review",
        "range make.implicit irr_loop memprof callsite pcsections DIAssignID callee_type alloc_token "
        "call_target "
        "block.uniformity.profile callgraph any",
    ),
]

INSTRUCTION_RULES = [
    R("control", "Ret UncondBr CondBr Switch Unreachable PHI"),
    R(
        "integer",
        "Add Sub Mul UDiv SDiv URem SRem Shl LShr AShr And Or Xor ICmp Trunc ZExt SExt Select BitCast",
    ),
    R("vector", "ExtractElement InsertElement ShuffleVector"),
    R("aggregate", "ExtractValue InsertValue"),
    R("freeze", "Freeze"),
    R("call", "Call"),
    R("memory", "Alloca Load Store GetElementPtr PtrToInt PtrToAddr"),
    R("float", "FNeg FCmp FAdd FSub FMul FDiv FRem FPToUI FPToSI UIToFP SIToFP FPTrunc FPExt"),
    R("memory model", "IntToPtr"),
    R("layout", "AddrSpaceCast"),
    R("concurrency", "Fence AtomicCmpXchg AtomicRMW"),
    R("exceptions", "Invoke Resume LandingPad CleanupRet CatchRet CatchSwitch CleanupPad CatchPad"),
    R("asm", "CallBr"),
    R("machine", "IndirectBr"),
    R("variadic", "VAArg"),
    R("not in IR", "UserOp1 UserOp2"),
]

TYPE_RULES = [
    R("integer", "Integer"),
    R("vector", "FixedVector"),
    R("control", "Void Label"),
    R("aggregate", "Struct"),
    R("call", "Function"),
    R("memory", "Pointer"),
    R("float", "Half BFloat Float Double FP128"),
    R("floating point", "X86_FP80 PPC_FP128"),
    R("scalable vector", "ScalableVector"),
    R("vector gap", "Array"),
    R("memory model", "Byte"),
    R("token", "Token"),
    R("other target", "X86_AMX TargetExt"),
    R("not in IR", "TypedPointer"),
    R("intrinsic operand", "Metadata"),
]

LINKAGE_RULES = [
    R("linkage", "External Internal Private"),
    R("odr copy", "LinkOnceODR WeakODR"),
    R("external", "AvailableExternally LinkOnceAny WeakAny Appending ExternalWeak Common"),
]

# Every calling convention CallingConv.h names, by name, so one added later fails until it's classified.
CALLING_CONVENTION_RULES = [
    R(
        "calling convention",
        "C Fast Cold GHC HiPE AnyReg PreserveMost PreserveAll Swift CXX_FAST_TLS Tail CFGuard_Check "
        "SwiftTail "
        "PreserveNone X86_StdCall X86_FastCall ARM_APCS ARM_AAPCS ARM_AAPCS_VFP MSP430_INTR X86_ThisCall "
        "PTX_Kernel PTX_Device SPIR_FUNC SPIR_KERNEL Intel_OCL_BI X86_64_SysV Win64 X86_VectorCall "
        "DUMMY_HHVM "
        "DUMMY_HHVM_C X86_INTR AVR_INTR AVR_SIGNAL AVR_BUILTIN AMDGPU_VS AMDGPU_GS AMDGPU_PS AMDGPU_CS "
        "AMDGPU_KERNEL X86_RegCall AMDGPU_HS MSP430_BUILTIN AMDGPU_LS AMDGPU_ES AArch64_VectorCall "
        "AArch64_SVE_VectorCall WASM_EmscriptenInvoke AMDGPU_Gfx M68k_INTR "
        "AArch64_SME_ABI_Support_Routines_PreserveMost_From_X0 "
        "AArch64_SME_ABI_Support_Routines_PreserveMost_From_X2 AMDGPU_CS_Chain AMDGPU_CS_ChainPreserve "
        "M68k_RTD GRAAL ARM64EC_Thunk_X64 ARM64EC_Thunk_Native RISCV_VectorCall "
        "AArch64_SME_ABI_Support_Routines_PreserveMost_From_X1 RISCV_VLSCall_32 RISCV_VLSCall_64 "
        "RISCV_VLSCall_128 RISCV_VLSCall_256 RISCV_VLSCall_512 RISCV_VLSCall_1024 RISCV_VLSCall_2048 "
        "RISCV_VLSCall_4096 RISCV_VLSCall_8192 RISCV_VLSCall_16384 RISCV_VLSCall_32768 RISCV_VLSCall_65536 "
        "AMDGPU_Gfx_WholeWave CHERIoT_CompartmentCall CHERIoT_CompartmentCallee CHERIoT_LibraryCall",
    )
]

CONSTANT_RULES = [
    R(
        "constant",
        "ConstantInt PoisonValue ConstantPointerNull ConstantAggregateZero ConstantDataVector "
        "ConstantVector ConstantStruct",
    ),
    R("global", "GlobalVariable ConstantDataArray ConstantArray"),
    R("call", "Function"),
    R("undef", "UndefValue"),
    R("float", "ConstantFP"),
    R("memory model", "ConstantByte"),
    R("external", "ConstantExpr GlobalIFunc DSOLocalEquivalent NoCFIValue"),
    R("alias", "GlobalAlias"),
    R("token", "ConstantTokenNone"),
    R("other target", "ConstantTargetNone"),
    R("pointer authentication", "ConstantPtrAuth"),
    R("machine", "BlockAddress"),
]

BUNDLE_RULES = [
    R("assume", "assume:nonnull assume:align assume:noundef"),
    R("no effect", "assume:cold assume:ignore"),
    R("memory model", "assume:dereferenceable assume:dereferenceable_or_null assume:separate_storage"),
    R("deoptimization", "deopt"),
    R("exceptions", "funclet"),
    R("gc", "gc-transition gc-live"),
    R("cfi", "cfguardtarget kcfi"),
    R("memory model", "preallocated"),
    R("objc", "clang.arc.attachedcall"),
    R("pointer authentication", "ptrauth deactivation-symbol"),
    R("convergence", "convergencectrl"),
]

# Forms: each with its class, and the probe that shows the emitter treats it so.
FORM_RULES = [
    R("vector", "udiv-of-vectors sdiv-of-vectors urem-of-vectors srem-of-vectors"),
    R("float shape", "intrinsic-lane-count-mismatch"),
    R("vector gap", "freeze-of-a-vector integer-bitcast-nondividing vector-constant-expression"),
    R("scalable", "getelementptr-over-a-scalable-type scalable-vector-in-a-recursive-function"),
    R("memory model", "load-of-a-scalable-vector"),
    R("aggregate gap", "array-value insertvalue-nested freeze-of-a-struct"),
    R(
        "layout",
        "pointer-in-address-space vector-of-pointers getelementptr-of-vectors "
        "data-layout-32-bit-pointers-with-memory data-layout-32-bit-addresses-with-memory "
        "data-layout-null-all-ones-with-memory",
    ),
    R("memory model", "store-of-i1 load-of-i1 freeze-of-a-pointer"),
    R("concurrency", "volatile-load volatile-store atomic-load atomic-store"),
    R("outside call", "call-to-a-declaration"),
    R("outside global", "external-global"),
    R("external", "call-to-an-odr-definition variadic-call alias-the-linker-may-replace"),
    R("variadic", "variadic-function"),
    R("exceptions", "personality-function"),
    R("big-endian", "big-endian-bitcast"),
    R("floating point", "float-setting-with-floating-point"),
    R("asm", "inline-asm-call"),
    R("gc", "function-with-gc"),
    R("machine", "prefix-or-prologue-data"),
    R("calling convention mismatch", "calling-convention-mismatch abi-attribute-mismatch"),
    R("attribute review", "speculatable-with-memory call-to-a-speculatable-function"),
    R("call", "indirect-call"),
    R("tail call", "tail-call musttail-call"),
    R("hint", "notail-call"),
    R("value promise", "noundef-on-a-vector range-on-a-vector noundef-on-a-struct"),
    R("undef", "undef-in-a-vector"),
    R("global", "getelementptr-constant-expression"),
    R("data layout", "data-layout-explicit-64-bit"),
]

RULES: dict[str, list[Rule]] = {
    "instruction": INSTRUCTION_RULES,
    "type": TYPE_RULES,
    "intrinsic": INTRINSIC_RULES,
    "attribute": ATTRIBUTE_RULES,
    "string attribute": STRING_ATTRIBUTE_RULES,
    "metadata": METADATA_RULES,
    "linkage": LINKAGE_RULES,
    "calling convention": CALLING_CONVENTION_RULES,
    "constant": CONSTANT_RULES,
    "operand bundle": BUNDLE_RULES,
    "form": FORM_RULES,
}

# ------------------------------------------------------------------------------------------------------------
# The items, from the pinned source.


def llvm_src() -> Path:
    src = os.environ.get("LLVM_PROJECT_SRC")
    if not src:
        sys.exit("LLVM_PROJECT_SRC isn't set: run inside nix develop")
    return Path(src)


def tblgen(src: Path, td: str) -> dict[str, Any]:
    include = src / "llvm" / "include"
    ran = proc.run(["llvm-tblgen", "--dump-json", "-I", include, include / "llvm" / "IR" / td], timeout=300)
    if not ran.ok:
        sys.exit(f"llvm-tblgen failed on {td}:\n{ran.err[-2000:]}")
    return json.loads(ran.out)


def enum_entries(text: str, start: str, suffix: str) -> list[str]:
    """The names in a C++ enum that starts at `start`, with `suffix` removed, in order."""
    body = text[text.index(start) :]
    body = body[: body.index("};")]
    body = re.sub(r"//[^\n]*|/\*.*?\*/", "", body, flags=re.S)
    return list(re.findall(rf"\b(\w+){suffix}\b", body))


def intrinsic_name(record: str, fields: dict[str, Any]) -> str:
    return fields.get("LLVMName") or "llvm." + record.removeprefix("int_").replace("_", ".")


@dataclass
class Item:
    kind: str
    name: str
    at: str = ""
    # Facts from the source the rules may use, which aren't written to the file.
    facts: dict[str, Any] = field(default_factory=dict)

    @property
    def key(self) -> tuple[str, str, str]:
        return (self.kind, self.at, self.name)


def derive(src: Path) -> list[Item]:
    include = src / "llvm" / "include" / "llvm" / "IR"
    items: list[Item] = []

    for op in re.findall(
        r"HANDLE_\w+_INST\s*\(\s*\d+\s*,\s*(\w+)\s*,", (include / "Instruction.def").read_text()
    ):
        items.append(Item("instruction", op))

    type_h = (include / "Type.h").read_text()
    for t in enum_entries(type_h, "enum TypeID {", "TyID"):
        items.append(Item("type", t))

    records = tblgen(src, "Intrinsics.td")
    for record in records["!instanceof"]["Intrinsic"]:
        fields = records[record]
        items.append(
            Item("intrinsic", intrinsic_name(record, fields), facts={"enum": record.removeprefix("int_")})
        )

    attrs = tblgen(src, "Attributes.td")
    for cls in ("EnumAttr", "IntAttr", "TypeAttr", "ConstantRangeAttr", "ConstantRangeListAttr"):
        for record in attrs["!instanceof"][cls]:
            fields = attrs[record]
            props = {p["def"] for p in fields.get("Properties", [])}
            name = fields["AttrString"]
            places = []
            if "FnAttr" in props:
                places += ["function", "call"]
            if "ParamAttr" in props:
                places += ["parameter", "call parameter"]
            if "RetAttr" in props:
                places += ["return", "call return"]
            for at in places:
                items.append(Item("attribute", name, at, {"kind": cls}))
    strings = [attrs[r]["AttrString"] for r in attrs["!instanceof"]["StrBoolAttr"]]
    for name in sorted(set(strings) | set(ALLOWED_STRINGS) | {"any"}):
        for at in ("function", "call"):
            items.append(Item("string attribute", name, at))
    for at in ("parameter", "return", "call parameter", "call return"):
        items.append(Item("string attribute", "any", at))

    fixed = (include / "FixedMetadataKinds.def").read_text()
    for name in re.findall(r'LLVM_FIXED_MD_KIND\s*\(\s*\w+\s*,\s*"([^"]+)"\s*,\s*\d+\s*\)', fixed):
        items.append(Item("metadata", name))
    for name in EMITTER_METADATA:
        items.append(Item("metadata", name))
    items.append(Item("metadata", "any"))

    global_value = (include / "GlobalValue.h").read_text()
    for linkage in enum_entries(global_value, "enum LinkageTypes {", "Linkage"):
        items.append(Item("linkage", linkage))

    cc_h = (include / "CallingConv.h").read_text()
    body = cc_h[cc_h.index("namespace CallingConv {") :]
    body = body[body.index("enum {") :]
    body = re.sub(r"//[^\n]*|/\*.*?\*/", "", body[: body.index("};")], flags=re.S)
    seen: set[int] = set()
    for name, number in re.findall(r"\b(\w+)\s*=\s*(\d+)\s*,", body):
        if name in ("FirstTargetCC", "MaxID") or int(number) in seen:
            continue
        seen.add(int(number))
        items.append(Item("calling convention", name, facts={"number": int(number)}))

    value_def = (include / "Value.def").read_text()
    for name in re.findall(
        r"^HANDLE_(?:GLOBAL_VALUE|CONSTANT|CONSTANT_EXCLUDE_LLVM_C_API)\((\w+)\)", value_def, re.M
    ):
        items.append(Item("constant", name))

    context = (src / "llvm" / "lib" / "IR" / "LLVMContext.cpp").read_text()
    for tag in re.findall(r"case LLVMContext::OB_\w+:\s*return \"([^\"]+)\";", context):
        items.append(Item("operand bundle", tag))
    bundles = (include / "BundleAttributes.def").read_text()
    for tag in re.findall(r"^ATTR\(\w+,\s*(\w+)\)", bundles, re.M):
        items.append(Item("operand bundle", "assume:" + tag))

    for rule in FORM_RULES:
        for name in sorted(rule.names):
            items.append(Item("form", name))

    keys = Counter(i.key for i in items)
    twice = [k for k, n in keys.items() if n > 1]
    if twice:
        sys.exit(f"items derived twice: {twice[:10]}")
    return items


# ------------------------------------------------------------------------------------------------------------
# Classifying.


def classify(items: list[Item]) -> tuple[list[dict[str, Any]], list[str]]:
    """Each item with its class, and what's wrong: items no rule or two rules match, and rules that are "
    "wrong."""
    problems = []
    for kind, rules in RULES.items():
        for rule in rules:
            if rule.reason not in REASONS:
                problems.append(f"{kind}: no reason {rule.reason!r}")
                continue
            if rule.prefixes and REASONS[rule.reason].cls != "refused":
                problems.append(
                    f"{kind}: a {REASONS[rule.reason].cls} rule matches by prefix, {rule.prefixes}"
                )
    out = []
    used: set[tuple[str, int, str]] = set()
    for item in items:
        rules = RULES[item.kind]
        here = [(n, r) for n, r in enumerate(rules) if not r.at or item.at in r.at]
        exact = [(n, r) for n, r in here if item.name in r.names]
        prefixed = [(n, r) for n, r in here if any(item.name.startswith(p) for p in r.prefixes)]
        found = exact or prefixed
        where = f"{item.kind} {item.at + ' ' if item.at else ''}{item.name}"
        if not found:
            problems.append(f"unclassified: {where}")
            continue
        if len(found) > 1:
            problems.append(
                f"two rules match {where}: {[REASONS[r.reason].cls + ' ' + r.reason for _, r in found]}"
            )
            continue
        n, rule = found[0]
        for name in rule.names:
            if name == item.name:
                used.add((item.kind, n, name))
        if rule.reason not in REASONS:
            continue
        reason = REASONS[rule.reason]
        row: dict[str, Any] = {"kind": item.kind}
        if item.at:
            row["at"] = item.at
        row["name"] = item.name
        row["class"] = reason.cls
        if reason.lane:
            row["lane"] = reason.lane
        row["reason"] = rule.reason
        out.append(row)
    present = {i.kind for i in items}
    for kind, rules in RULES.items():
        if kind not in present:
            continue
        for n, rule in enumerate(rules):
            for name in rule.names:
                if (kind, n, name) not in used:
                    problems.append(
                        f"{kind}: rule {rule.reason!r} names {name!r}, which the pin doesn't have there"
                    )
    return out, problems


def document(rows: list[dict[str, Any]]) -> dict[str, Any]:
    llvm = pins.llvm()
    totals: Counter[str] = Counter(r["class"] for r in rows)
    by_kind: dict[str, Counter[str]] = defaultdict(Counter)
    lanes: Counter[str] = Counter()
    for r in rows:
        by_kind[r["kind"]][r["class"]] += 1
        if r.get("lane"):
            lanes[r["lane"]] += 1
    return {
        "schema": SCHEMA,
        "pin": {"tag": llvm["tag"], "commit": llvm["commit"]},
        "generated_by": "tests/ir_features.py generate",
        "classes": CLASSES,
        "lanes": LANES,
        "reasons": {
            k: {"class": v.cls, **({"lane": v.lane} if v.lane else {}), "says": v.says}
            for k, v in REASONS.items()
        },
        "totals": {
            "items": len(rows),
            **{c: totals[c] for c in CLASSES},
            "by_kind": {k: {c: by_kind[k][c] for c in CLASSES if by_kind[k][c]} for k in KINDS},
            "refused_by_lane": dict(sorted(lanes.items())),
        },
        "items": rows,
    }


def render(doc: dict[str, Any]) -> str:
    """The file, with one item to a line, so a change shows as the lines it changes."""
    head = {k: v for k, v in doc.items() if k != "items"}
    text = json.dumps(head, indent=1)
    lines = ",\n".join("  " + json.dumps(r, separators=(", ", ": ")) for r in doc["items"])
    return text[:-2] + ',\n "items": [\n' + lines + "\n ]\n}\n"


# ------------------------------------------------------------------------------------------------------------
# Probes. Each is a module whose function `probe` uses the item, and as little else as possible. A probe can
# have versions, tried in order: the first LLVM's verifier accepts decides.

ATTRIBUTE_TEXT = {
    "align": "align 4",
    "alignstack": "alignstack(8)",
    "allockind": 'allockind("alloc")',
    "allocsize": "allocsize(0)",
    "captures": "captures(none)",
    "denormal_fpenv": "denormal_fpenv(preservesign)",
    "dereferenceable": "dereferenceable(4)",
    "dereferenceable_or_null": "dereferenceable_or_null(4)",
    "memory": "memory(none)",
    "nofpclass": "nofpclass(nan)",
    "uwtable": "uwtable",
    "optnone": "optnone noinline",
    "vscale_range": "vscale_range(1,16)",
    "byref": "byref(i32)",
    "byval": "byval(i32)",
    "elementtype": "elementtype(i32)",
    "inalloca": "inalloca(i32)",
    "preallocated": "preallocated(i32)",
    "sret": "sret(i32)",
    "initializes": "initializes((0, 4))",
    "dead_on_return": "dead_on_return",
}


def attribute_text(name: str, ty: str) -> str:
    if name == "range":
        scalar = re.sub(r"<\d+ x (\w+)>", r"\1", ty)
        return f"range({scalar} 0, 10)"
    return ATTRIBUTE_TEXT.get(name, name)


VALUE_TYPES = ("i32", "ptr", "i64", "float")


# A value each string attribute accepts.
STRING_VALUES = {
    "alloc-family": "malloc",
    "frame-pointer": "all",
    "min-legal-vector-width": "0",
    "no-builtins": "true",
    "no-trapping-math": "true",
    "probe-stack": "inline-asm",
    "stack-protector-buffer-size": "8",
    "target-cpu": "x86-64",
    "target-features": "+sse2",
    "tune-cpu": "generic",
    "zero-call-used-regs": "skip",
}


def attribute_probes(item: Item) -> list[str]:
    a, at = item.name, item.at
    out = []
    if item.kind == "string attribute":
        text = '"x-unknown"="1"' if a == "any" else f'"{a}"="{STRING_VALUES.get(a, "true")}"'
        if at in ("function", "call"):
            group = f"attributes #0 = {{ {text} }}"
            if at == "function":
                return [f"define void @probe() #0 {{\n  ret void\n}}\n{group}\n"]
            return [
                f"define void @callee() {{\n  ret void\n}}\n"
                f"define void @probe() {{\n  call void @callee() #0\n  ret void\n}}\n{group}\n"
            ]
        return value_probes(at, ["i32"], lambda ty: text)
    if (a, at) == ("jumptable", "call"):
        # LLVM's verifier checks `jumptable` with `cast<GlobalValue>(V)->hasGlobalUnnamedAddr()`, and at a
        # call `V` is the call, so the bits it reads aren't the call's. Whether a probe passes the verifier
        # can change from run to run, as on macOS, or from shape to shape, as on Linux, so no probe is built.
        return []
    if at in ("function", "call"):
        # In an attribute group, alignstack is written with `=`.
        text = "alignstack=8" if a == "alignstack" else ATTRIBUTE_TEXT.get(a, a)
        group = f"attributes #0 = {{ {text} }}"
        shapes = [
            ("void", "", "ret void"),
            ("ptr", "i64 %n", "ret ptr null"),
            ("i32", "i32 %n", "ret i32 %n"),
        ]
        for ret, params, body in shapes:
            if at == "function":
                out.append(f"define {ret} @probe({params}) #0 {{\n  {body}\n}}\n{group}\n")
                out.append(f"define {ret} @probe({params}) unnamed_addr #0 {{\n  {body}\n}}\n{group}\n")
            else:
                args = ", ".join(f"{p.split()[0]} {p.split()[1]}" for p in params.split(",") if p.strip())
                call = (
                    f"call {ret} @callee({args}) #0"
                    if ret == "void"
                    else f"%r = call {ret} @callee({args}) #0"
                )
                out.append(
                    f"define {ret} @callee({params}) {{\n  {body}\n}}\n"
                    f"define {ret} @probe({params}) {{\n  {call}\n  {body}\n}}\n{group}\n"
                )
        return out
    return value_probes(
        at, [*VALUE_TYPES, "<4 x i32>"], lambda ty: attribute_text(a, ty), a in ABI_ATTRIBUTES
    )


# Attributes that have to be the same at a call and on the callee, or LangRef says the behavior may be
# undefined, so a probe at a call puts them on the callee too. The form abi-attribute-mismatch probes one that
# isn't.
ABI_ATTRIBUTES = {"signext", "zeroext", "noext", "inreg", "alignstack"}


def value_probes(at: str, types: list[str], text: Callable[[str], str], abi: bool = False) -> list[str]:
    out = []
    for ty in types:
        t = text(ty)
        on_callee = f"{t} " if abi else ""
        if at == "parameter":
            out.append(f"define void @probe({ty} {t} %x) {{\n  ret void\n}}\n")
            out.append(f"define {ty} @probe({ty} {t} %x) {{\n  ret {ty} %x\n}}\n")
            out.append(f"define void @probe(ptr %a, {ty} {t} %x) {{\n  ret void\n}}\n")
        elif at == "return":
            out.append(f"define {t} {ty} @probe({ty} %x) {{\n  ret {ty} %x\n}}\n")
        elif at == "call parameter":
            out.append(
                f"define void @callee({ty} {on_callee}%x) {{\n  ret void\n}}\n"
                f"define void @probe({ty} %x) {{\n  call void @callee({ty} {t} %x)\n  ret void\n}}\n"
            )
        elif at == "call return":
            out.append(
                f"define {on_callee}{ty} @callee({ty} %x) {{\n  ret {ty} %x\n}}\n"
                f"define {ty} @probe({ty} %x) {{\n  %r = call {t} {ty} @callee({ty} %x)\n  ret {ty} %r\n}}\n"
            )
    return out


# For each kind, how to attach it, as tried in order; `{md}` is the node.
METADATA_NODES = {
    "tbaa": '!{!1, !1, i64 0}\n!1 = !{!"int", !2, i64 0}\n!2 = !{!"root"}',
    "prof": '!{!"branch_weights", i32 1, i32 2}',
    "fpmath": "!{float 2.5}",
    "range": "!{i32 0, i32 10}",
    "nontemporal": "!{i32 1}",
    "dereferenceable": "!{i64 4}",
    "dereferenceable_or_null": "!{i64 4}",
    "align": "!{i64 8}",
    "llvm.loop": 'distinct !{!0, !1}\n!1 = !{!"llvm.loop.unroll.disable"}',
    "type": '!{i64 0, !"t"}',
    "section_prefix": '!{!"function_section_prefix", !"hot"}',
    "irr_loop": '!{!"loop_header_weight", i64 100}',
    "alias.scope": "!{!1}\n!1 = distinct !{!1, !2}\n!2 = distinct !{!2}",
    "noalias": "!{!1}\n!1 = distinct !{!1, !2}\n!2 = distinct !{!2}",
    "llvm.access.group": "distinct !{}",
    "llvm.mem.parallel_loop_access": "distinct !{}",
    "callees": "!{ptr @callee}",
    "associated": "!{ptr @callee}",
    "annotation": '!{!"a"}',
    "kcfi_type": "!{i32 12345}",
    "vcall_visibility": "!{i64 0}",
    "absolute_symbol": "!{i64 0, i64 256}",
    "noalias.addrspace": "!{i32 5, i32 6}",
    "mmra": '!{!"foo", !"bar"}',
    "memprof": '!{!1}\n!1 = !{!2, !"notcold"}\n!2 = !{i64 1, i64 2}',
    "callsite": "!{i64 1}",
    "callback": "!{!1}\n!1 = !{i64 0, i1 false}",
    "func_sanitize": "!{i32 1, i32 2}",
    "guid": "!{i64 1}",
    "callee_type": '!{!1}\n!1 = !{i64 0, !"_ZTSFvvE.generalized"}',
    "pcsections": '!{!"s"}',
    "captures": '!{!"address"}',
    "nofpclass": "!{i32 3}",
    "alloc_token": '!{!"t", i1 false}',
    "elf_section_properties": "!{i32 1, i32 2}",
    "implicit.ref": "!{ptr @callee}",
}


# Where a kind of metadata goes, for kinds without a probe in probes.ll: on each kind of instruction LLVM's
# verifier might allow it on, as `MD`. Metadata the emitter reads only on instructions is put nowhere else, so
# a probe can't pass by putting it where the emitter doesn't look.
ON_INSTRUCTIONS = [
    "define i32 @probe(ptr %p) {\n  %v = load i32, ptr %p, MD\n  ret i32 %v\n}\n",
    "define ptr @probe(ptr %p) {\n  %v = load ptr, ptr %p, MD\n  ret ptr %v\n}\n",
    "define void @probe(ptr %p, i32 %v) {\n  store i32 %v, ptr %p, MD\n  ret void\n}\n",
    "define void @probe(i1 %c) {\n  br i1 %c, label %a, label %b, MD\na:\n  ret void\nb:\n  ret void\n}\n",
    "define void @probe(i1 %c) {\nentry:\n  br label %h\nh:\n  br i1 %c, label %h, label %x, MD\nx:\n"
    "  ret void\n}\n",
    "define void @probe() {\n  call void @callee(), MD\n  ret void\n}\n",
    "define void @probe(ptr %f) {\n  call void %f(), MD\n  ret void\n}\n",
    "define i32 @probe(i32 %a) {\n  %r = add i32 %a, 1, MD\n  ret i32 %r\n}\n",
    "define float @probe(float %a) {\n  %r = fadd float %a, %a, MD\n  ret float %r\n}\n",
    "define float @probe(ptr %p) {\n  %v = load float, ptr %p, MD\n  ret float %v\n}\n",
]
# And for metadata that goes on a function or a global, there first.
ON_SYMBOLS = [
    "define void @probe() MD {\n  ret void\n}\n",
    "@g = global i32 0, MD\ndefine i32 @probe() {\n  %v = load i32, ptr @g\n  ret i32 %v\n}\n",
    "@g = external global i32, MD\ndefine ptr @probe() {\n  ret ptr @g\n}\n",
]
SYMBOL_METADATA = {
    "type",
    "section_prefix",
    "associated",
    "vcall_visibility",
    "func_sanitize",
    "exclude",
    "kcfi_type",
    "implicit.ref",
    "elf_section_properties",
    "guid",
    "callback",
    "absolute_symbol",
}


def metadata_probes(name: str) -> list[str]:
    kind = "foo" if name == "any" else name
    nodes = [METADATA_NODES[kind]] if kind in METADATA_NODES else []
    nodes += ["!{}", "distinct !{}", '!{!"x"}', "!{i64 1}"]
    places = ON_SYMBOLS + ON_INSTRUCTIONS if kind in SYMBOL_METADATA else ON_INSTRUCTIONS
    callee = "define void @callee() {\n  ret void\n}\n"
    return [
        callee + place.replace("MD", f"!{kind} !0") + f"!0 = {node}\n" for place in places for node in nodes
    ]


def calling_convention_probes(number: int) -> list[str]:
    params = ["", "ptr byval(i8) %p", "ptr byval(i8) %p, i64 %e", "ptr swiftself %p", "i1 %a"]
    return [f"define cc {number} void @probe({p}) {{\n  ret void\n}}\n" for p in params]


PROBES_FILE = ROOT / "tests" / "ir_features" / "probes.ll"


def written_probes() -> dict[tuple[str, str], list[str]]:
    """The probes in probes.ll, by kind and name, each a list of versions."""
    out: dict[tuple[str, str], list[str]] = {}
    key: tuple[str, str] | None = None
    for line in PROBES_FILE.read_text().splitlines(keepends=True):
        if line.startswith("; probe: "):
            kind, name = line.removeprefix("; probe: ").strip().split(" / ")
            key = (kind, name)
            if key in out:
                sys.exit(f"{PROBES_FILE.name} has two probes for {kind} {name}")
            out[key] = [""]
        elif line.startswith("; or:"):
            if key is None:
                sys.exit(f"{PROBES_FILE.name}: `; or:` before any probe")
            out[key].append("")
        elif key is not None:
            out[key][-1] += line
    return {k: [v.strip() + "\n" for v in vs] for k, vs in out.items()}


def text_probes(item: Item, written: dict[tuple[str, str], list[str]]) -> list[str] | None:
    """The versions of an item's probe: written in probes.ll, or built here. None for an intrinsic that
    ir-lean-probe builds instead."""
    if (item.kind, item.name) in written:
        return written[(item.kind, item.name)]
    if item.kind == "intrinsic":
        return None
    if item.kind in ("attribute", "string attribute"):
        return attribute_probes(item)
    if item.kind == "metadata":
        return metadata_probes(item.name)
    if item.kind == "calling convention":
        return calling_convention_probes(item.facts["number"])
    return []


# ------------------------------------------------------------------------------------------------------------
# Running probes.


@dataclass
class Outcome:
    status: str  # ok, refused, invalid, missing
    detail: str = ""
    lean: str = ""  # the Lean the emitter printed, for ok


def report(tool: Path, path: Path, function: str = "probe") -> Outcome:
    ran = proc.run([str(tool), str(path), "--report"], timeout=120)
    # The emitter exits 1 on IR LLVM's reader or verifier rejects. Anything else is a crash or a hang.
    if ran.limit or ran.exit not in (0, 1):
        return Outcome(
            "crash", f"the emitter {'hit its ' + str(ran.limit) if ran.limit else f'exited {ran.exit}'}"
        )
    if ran.exit == 1:
        said = (ran.err or ran.out).strip().splitlines()
        return Outcome("invalid", said[0][:300] if said else "exit 1")
    for line in ran.out.splitlines():
        row = line.split("\t")
        if len(row) >= 3 and row[1] == function:
            return Outcome("ok" if row[0] == "ok" else "refused", row[-1] if row[0] != "ok" else row[3])
    return Outcome("missing", ran.out[-300:])


def first_valid(tool: Path, work: Path, n: int, variants: list[str]) -> tuple[Outcome, Path | None]:
    last = Outcome("invalid", "no probe")
    for v, text in enumerate(variants):
        path = work / f"p{n}_{v}.ll"
        path.write_text(text)
        out = report(tool, path)
        if out.status != "invalid":
            return out, path if out.status != "crash" else None
        last = out
    return last, None


def lean_of(tool: Path, path: Path, namespace: str) -> tuple[str, list[str]]:
    """The Lean the emitter prints for `path`, without its header, under `namespace`."""
    out = path.with_suffix(".lean")
    ran = proc.run([str(tool), str(path), "--no-code", "--namespace", namespace, "-o", str(out)], timeout=300)
    if ran.limit or ran.exit not in (0, 3) or not out.exists():
        return "", [f"the emitter failed on {path.name}: {ran.err[-300:]}"]
    text = out.read_text()
    start = text.index(f"namespace {namespace}\n")
    return text[start:], []


def elaborate(sections: dict[str, str], work: Path) -> dict[str, list[str]]:
    """Elaborates every namespace in one Lean file, and returns the errors in each."""
    header = (
        "import IRLean\n\nopen IRLean\n\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n"
        "set_option linter.unusedVariables false\nset_option genInjectivity false\nset_option genSizeOf "
        "false\n"
        "set_option genSizeOfSpec false\n\n"
    )
    text, starts = header, []
    for ns, body in sections.items():
        starts.append((text.count("\n") + 1, ns))
        text += body + "\n"
    path = work / "Probes.lean"
    path.write_text(text)
    ran = proc.run(lean.argv(6000, path), timeout=1800, env=lean.env(), cwd=ROOT)
    if ran.limit:
        sys.exit(f"Lean ran out of {ran.limit} elaborating the probes")
    errors: dict[str, list[str]] = defaultdict(list)
    lines = text.splitlines()
    for line in lean.errors(ran.out + ran.err):
        m = re.match(r".*?:(\d+):\d+: error", line)
        where = int(m.group(1)) if m else 0
        ns = next((n for start, n in reversed(starts) if start <= where), "?")
        # The function it's in: the last namespace the emitter opened for one before the error.
        fn = next(
            (x[len("namespace ") :] for x in reversed(lines[:where]) if x.startswith("namespace ")), "?"
        )
        errors[ns].append(f"in {fn}: {line.split(': error: ', 1)[-1][:200]}")
    if ran.exit != 0 and not errors:
        errors["?"].append((ran.out + ran.err)[-500:])
    return errors


def run_probes(
    items: list[Item],
    rows: list[dict[str, Any]],
    tool: Path,
    probe_tool: Path,
    work: Path,
    with_lean: bool,
    verbose: bool = False,
) -> tuple[list[str], dict[str, Any]]:
    """What's wrong, and the counts."""
    classes = {(r["kind"], r.get("at", ""), r["name"]): r for r in rows}
    problems: list[str] = []
    outcomes: dict[tuple[str, str, str], list[tuple[str, Outcome, Path | None]]] = defaultdict(list)

    # Intrinsics: one module, from ir-lean-probe.
    module = work / "intrinsics.ll"
    gen = proc.run([str(probe_tool), "-o", str(module)], timeout=1200)
    if gen.limit or gen.exit != 0:
        sys.exit(f"ir-lean-probe failed: {gen.err[-1000:]}")
    unprobed = {}
    for line in gen.err.splitlines():
        if line.startswith("unprobed\t"):
            _, name, why = line.split("\t", 2)
            unprobed[name] = why
    ran = proc.run([str(tool), str(module), "--report"], timeout=1200)
    if ran.limit or ran.exit != 0:
        sys.exit(f"the emitter failed on the intrinsic probes: {ran.err[-1000:]}")
    for line in ran.out.splitlines():
        row = line.split("\t")
        if len(row) < 3 or not row[1].startswith("intrinsic|"):
            continue
        _, name, shape = row[1].split("|")
        out = Outcome("ok" if row[0] == "ok" else "refused", row[-1] if row[0] != "ok" else row[3])
        outcomes[("intrinsic", "", name)].append((shape, out, module))

    # Everything else: a module each.
    written = written_probes()
    known = {(i.kind, i.name) for i in items}
    for kind, name in sorted(written.keys() - known):
        problems.append(f"{PROBES_FILE.name} has a probe for {kind} {name}, which isn't an item")
    jobs = [
        (n, item, text_probes(item, written))
        for n, item in enumerate(items)
        if item.kind != "intrinsic" or (item.kind, item.name) in written
    ]

    def one(job: tuple[int, Item, list[str] | None]) -> tuple[Item, Outcome, Path | None]:
        n, item, variants = job
        if not variants:
            return item, Outcome("invalid", "no probe written"), None
        out, path = first_valid(tool, work, n, variants)
        return item, out, path

    with concurrent.futures.ThreadPoolExecutor(max_workers=min(16, os.cpu_count() or 4)) as pool:
        for item, out, path in pool.map(one, jobs):
            outcomes[item.key].append(("", out, path))

    # The Lean for every probe the emitter translated.
    sections: dict[str, str] = {}
    owner: dict[str, list[tuple[str, str, str]]] = defaultdict(list)
    if with_lean:
        text, errs = lean_of(tool, module, "Intrinsics")
        problems += errs
        if text:
            sections["Intrinsics"] = text
            for key, outs in outcomes.items():
                if key[0] == "intrinsic" and any(o.status == "ok" for _, o, _ in outs):
                    owner["Intrinsics"].append(key)
        for n, (key, outs) in enumerate(sorted(outcomes.items())):
            for _, out, path in outs:
                if out.status == "ok" and path is not None and path != module:
                    ns = f"P{n}"
                    text, errs = lean_of(tool, path, ns)
                    problems += errs
                    sections[ns] = text
                    owner[ns].append(key)
        errors = elaborate(sections, work)
        # The intrinsic probes share one namespace: an error there names its function.
        for ns, errs in errors.items():
            if ns == "Intrinsics":
                for e in errs:
                    problems.append(f"Lean rejects what the emitter printed for an intrinsic probe: {e}")
            else:
                for key in owner.get(ns, [("?", "", ns)]):
                    problems.append(f"Lean rejects what the emitter printed for {key}: {errs[0]}")

    cases = emitter_cases(items)
    counts: Counter[str] = Counter()
    unprobed_items: list[str] = []
    for item in items:
        row = classes.get(item.key)
        if row is None:
            continue
        cls = row["class"]
        outs = outcomes.get(item.key, [])
        where = f"{item.kind} {item.at + ' ' if item.at else ''}{item.name}"
        for _, o, _ in outs:
            if o.status in ("crash", "missing"):
                problems.append(
                    f"{where}: {o.detail if o.status == 'crash' else 'the emitter reported no probe'}"
                )
        valid = [(s, o) for s, o, _ in outs if o.status in ("ok", "refused")]
        if not valid:
            why = (
                unprobed.get(item.name, "no probe")
                if item.kind == "intrinsic" and not outs
                else (outs[0][1].detail if outs else "no probe")
            )
            counts["unprobed"] += 1
            unprobed_items.append(f"{where} ({cls}): {why}")
            # An intrinsic ir-lean-probe can build no call to is refused by the emitter's default, which
            # refuses every intrinsic `emitIntrinsic` has no case for. Anything else needs its reason in
            # UNPROBEABLE.
            if item.kind == "intrinsic" and item.name in unprobed and not outs:
                if cls != "refused" or item.name in cases:
                    problems.append(f"{where} is {cls}, and no probe of it shows that: {why}")
            elif item.key not in UNPROBEABLE:
                problems.append(f"{where} has no probe the emitter reads: {why}")
            continue
        if item.key in UNPROBEABLE:
            problems.append(f"{where} is listed in UNPROBEABLE, and has a probe: drop it from the list")
        counts["probed"] += 1
        oks = [s for s, o in valid if o.status == "ok"]
        refusals = [(s, o.detail) for s, o in valid if o.status == "refused"]
        if cls == "refused":
            if oks:
                problems.append(f"{where} is refused, and the emitter translates it ({', '.join(oks)})")
        elif not oks:
            problems.append(f"{where} is {cls}, and the emitter refuses it: {refusals[0][1]}")
        else:
            # A modeled intrinsic may be refused at some shapes only for something classified refused: a type,
            # or a form.
            for shape, detail in refusals:
                because = next((k for rx, k in PARTIAL if re.search(rx, detail)), None)
                if because is None or classes.get(because, {}).get("class") != "refused":
                    problems.append(f"{where} is {cls}, and the emitter refuses it at {shape}: {detail}")
    if verbose:
        print("\n".join(f"unprobed: {u}" for u in unprobed_items))
    return problems, dict(counts)


# Why a modeled item's probe may be refused at some shapes: the emitter's reason, and the refused item it's
# about.
PARTIAL = [
    (r"^type (<(vscale x )?\d+ x )?x86_fp80>?$", ("type", "", "X86_FP80")),
    (r"^type (<(vscale x )?\d+ x )?ppc_fp128>?$", ("type", "", "PPC_FP128")),
    (r"^type <vscale x \d+ x ptr", ("form", "", "vector-of-pointers")),
    (r"^type <\d+ x ptr", ("form", "", "vector-of-pointers")),
    (
        r"^intrinsic llvm\.\S+ with another number of lanes than its argument$",
        ("form", "", "intrinsic-lane-count-mismatch"),
    ),
    (r"^type ptr addrspace", ("form", "", "pointer-in-address-space")),
]

# Items no probe can show anything about, each with why. Every other item without one fails the check.
UNPROBEABLE = {
    ("instruction", "", "UserOp1"): "internal to LLVM's passes: neither IR's text nor its bitcode has it",
    ("instruction", "", "UserOp2"): "internal to LLVM's passes: neither IR's text nor its bitcode has it",
    ("type", "", "TypedPointer"): "gone from IR's text and bitcode, used only inside some GPU backends",
    (
        "type",
        "",
        "Metadata",
    ): "only an operand of an intrinsic, and no intrinsic the emitter translates takes one",
    (
        "attribute",
        "parameter",
        "immarg",
    ): "only on an intrinsic's declaration; LLVM's verifier rejects it here",
    (
        "attribute",
        "call parameter",
        "immarg",
    ): "only on an intrinsic's declaration; LLVM's verifier rejects it here",
    ("attribute", "function", "builtin"): "only at a call; LLVM's verifier rejects it on a function",
    ("attribute", "call", "speculatable"): "only on a function; LLVM's verifier rejects it at a call",
    (
        "attribute",
        "call",
        "jumptable",
    ): "LLVM's verifier reads memory that isn't the call's to check it, so no probe of it is the same "
    "every run; checkFunctionAttributes has no case for it, so the emitter refuses it",
    ("attribute", "call", "denormal_fpenv"): "only on a function; LLVM's verifier rejects it at a call",
    (
        "attribute",
        "call",
        "preallocated",
    ): "at a call only on llvm.call.preallocated.arg, which the verifier checks",
    ("attribute", "parameter", "elementtype"): "only on an intrinsic's or inline assembly's arguments",
    ("attribute", "call parameter", "elementtype"): "only on an intrinsic's or inline assembly's arguments",
    ("attribute", "return", "elementtype"): "only on an intrinsic's or inline assembly's arguments",
    (
        "attribute",
        "call parameter",
        "returned",
    ): "needs a call whose argument and result types match, which the "
    "probes' callees don't have, and it's refused at every call",
    ("attribute", "call parameter", "swifterror"): "needs a swifterror alloca, which needs memory",
    ("attribute", "call parameter", "preallocated"): "needs llvm.call.preallocated.setup's token",
}


def emitter_cases(items: list[Item]) -> set[str]:
    """The intrinsics `emitIntrinsic` has a case for, by name."""
    text = EMITTER.read_text()
    body = text[text.index("bool FunctionEmitter::emitIntrinsic") :]
    body = body[: body.index("\n}\n")]
    enums = {i.facts["enum"]: i.name for i in items if i.kind == "intrinsic"}
    return {enums[c] for c in re.findall(r"case Intrinsic::(\w+):", body) if c in enums}


def static_checks(rows: list[dict[str, Any]], items: list[Item]) -> list[str]:
    """The emitter's own list of intrinsics against the modeled ones: each modeled intrinsic needs a case in
    `emitIntrinsic`, and each case has to be classified, so one added there without a class here fails."""
    text = EMITTER.read_text()
    body = text[text.index("bool FunctionEmitter::emitIntrinsic") :]
    body = body[: body.index("\n}\n")]
    cases = set(re.findall(r"case Intrinsic::(\w+):", body))
    enums = {i.facts["enum"]: i.name for i in items if i.kind == "intrinsic"}
    names = emitter_cases(items)
    problems = [
        f"emitIntrinsic has a case for {c}, which the pin doesn't define" for c in sorted(cases - set(enums))
    ]
    cls = {r["name"]: r["class"] for r in rows if r["kind"] == "intrinsic"}
    upgraded = {
        r["name"] for r in rows if r["kind"] == "intrinsic" and r["reason"] in ("upgraded", "upgraded debug")
    }
    for name in sorted(n for n, c in cls.items() if c == "modeled"):
        if name not in names and name not in upgraded:
            problems.append(f"{name} is modeled, and emitIntrinsic has no case for it")
    for name in sorted(names):
        if cls.get(name) not in ("modeled", "refused"):
            problems.append(f"emitIntrinsic has a case for {name}, which is {cls.get(name)}")
    return problems


# ------------------------------------------------------------------------------------------------------------


def build() -> tuple[list[Item], dict[str, Any], list[str]]:
    items = derive(llvm_src())
    rows, problems = classify(items)
    return items, document(rows), problems


def cmd_generate(args: argparse.Namespace) -> int:
    _, doc, problems = build()
    if problems:
        print("\n".join(problems[:200]), file=sys.stderr)
        print(f"{len(problems)} problems; nothing written", file=sys.stderr)
        return 1
    FILE.write_text(render(doc))
    print(json.dumps(doc["totals"], indent=1))
    return 0


def cmd_check(args: argparse.Namespace) -> int:
    items, doc, problems = build()
    if not FILE.exists():
        problems.append(f"{FILE.relative_to(ROOT)} is missing: run tests/ir_features.py generate")
    elif FILE.read_text() != render(doc):
        old = json.loads(FILE.read_text())
        before = {(r["kind"], r.get("at", ""), r["name"]): r for r in old.get("items", [])}
        after = {(r["kind"], r.get("at", ""), r["name"]): r for r in doc["items"]}
        for k in sorted(after.keys() - before.keys())[:50]:
            problems.append(f"not in the file: {' '.join(x for x in k if x)}")
        for k in sorted(before.keys() - after.keys())[:50]:
            problems.append(f"in the file, and not at the pin: {' '.join(x for x in k if x)}")
        for k in sorted(before.keys() & after.keys()):
            if before[k] != after[k]:
                problems.append(f"changed: {before[k]} -> {after[k]}")
        problems.append(
            f"{FILE.relative_to(ROOT)} differs from what the pin and the rules give: run generate"
        )
    problems += static_checks(doc["items"], items)
    with tempfile.TemporaryDirectory(prefix="ir-features-") as tmp:
        found, counts = run_probes(
            items,
            doc["items"],
            args.tool.resolve(),
            args.probe.resolve(),
            Path(tmp),
            not args.no_lean,
            args.verbose,
        )
    problems += found
    totals = doc["totals"]
    print(
        f"{totals['items']} items: {totals['modeled']} modeled, {totals['assumed']} assumed, "
        f"{totals['refused']} "
        f"refused. {counts.get('probed', 0)} probed, {counts.get('unprobed', 0)} without a probe"
    )
    for p in problems[:300]:
        print("FAIL ", p)
    if problems:
        print(f"{len(problems)} problems")
        return 1
    print("every item is classified, and the emitter does what each class says")
    return 0


def cmd_summary(args: argparse.Namespace) -> int:
    doc = json.loads(FILE.read_text())
    schemas.check(doc, SCHEMA)
    print(json.dumps(doc["totals"], indent=1))
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("generate")
    c = sub.add_parser("check")
    c.add_argument("--tool", type=Path, default=ROOT / "build" / "ir-lean")
    c.add_argument("--probe", type=Path, default=ROOT / "build" / "ir-lean-probe")
    c.add_argument("--no-lean", action="store_true", help="don't elaborate what the emitter prints")
    c.add_argument("--verbose", action="store_true", help="list the items no probe could be built for")
    sub.add_parser("summary")
    args = ap.parse_args()
    return {"generate": cmd_generate, "check": cmd_check, "summary": cmd_summary}[args.cmd](args)


if __name__ == "__main__":
    sys.exit(main())
