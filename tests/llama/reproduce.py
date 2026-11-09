#!/usr/bin/env python3
"""Reproduce the pinned Clang 23.1.5 llama.cpp Q5 rewrite on Linux/Zen 5.

Run in the project's Nix dev shell. Phases consume artifacts from earlier phases;
all runs prepare, build, rewrite, check and bench in order. --reuse-build skips
compilation in build/all after validating the existing checkout and build flags.
No compiler is downloaded: --llvm-bin selects an installed LLVM 23.1.5 toolchain.
New builds retain the dev shell's Nix Clang 23.1.3 wrapper and resource headers.
Check/bench save new run directories and never overwrite earlier inference runs.
"""

import argparse
import hashlib
import json
import os
import re
import shlex
import shutil
import struct
import subprocess
import sys
import time
import urllib.request
from pathlib import Path

import measure

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parents[1]
REVISION = "80d2c0c2c56e4a1bbf74be98f64b99927bf230bc"
SOURCE_URL = "https://github.com/ggml-org/llama.cpp.git"
MODEL_REVISION = "9217f5db79a29953eb74d5343926648285ec7e67"
MODEL_NAME = "qwen2.5-0.5b-instruct-q4_k_m.gguf"
MODEL_URL = f"https://huggingface.co/Qwen/Qwen2.5-0.5B-Instruct-GGUF/resolve/{MODEL_REVISION}/{MODEL_NAME}"
MODEL_SHA256 = "74a4da8c9fdbcd15bd1f6d01d621410d31c6fc00986f5eb687824e7b93d7a9db"
NATIVE_ENV = {"NIX_ENFORCE_NO_NATIVE": "0", "NIX_ENFORCE_NO_NATIVE_x86_64_unknown_linux_gnu": "0"}
ON = ("GGML_CPU", "GGML_NATIVE", "GGML_CPU_REPACK", "GGML_LLAMAFILE")
OFF = (
    "GGML_BACKEND_DL",
    "GGML_BLAS",
    "GGML_CUDA",
    "GGML_VULKAN",
    "GGML_METAL",
    "GGML_HIP",
    "GGML_SYCL",
    "GGML_MUSA",
    "GGML_OPENCL",
    "GGML_OPENVINO",
    "GGML_WEBGPU",
    "GGML_RPC",
    "GGML_HEXAGON",
    "GGML_VIRTGPU",
    "GGML_ZDNN",
    "GGML_ZENDNN",
    "GGML_LTO",
    "GGML_CPU_ALL_VARIANTS",
    "LLAMA_BUILD_APP",
    "LLAMA_BUILD_SERVER",
    "LLAMA_BUILD_UI",
    "LLAMA_BUILD_MTMD",
    "LLAMA_OPENSSL",
)


def file_hash(path):
    with path.open("rb") as handle:
        return hashlib.file_digest(handle, "sha256").hexdigest()


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def compilation_args(entry):
    return list(entry["arguments"]) if "arguments" in entry else shlex.split(entry["command"])


def allocated_sections(path):
    """Read ELF64 little-endian allocated section bytes, without external Python packages."""
    data = path.read_bytes()
    if data[:6] != b"\x7fELF\x02\x01":
        raise ValueError(f"expected ELF64 little-endian object: {path}")
    header = struct.unpack_from("<HHIQQQIHHHHHH", data, 16)
    machine, offset, entry_size, count, names_index = header[1], header[5], header[10], header[11], header[12]
    if machine != 62 or entry_size != 64 or count == 0 or names_index >= count:
        raise ValueError(f"unsupported ELF section table: {path}")
    sections = [struct.unpack_from("<IIQQQQIIQQ", data, offset + i * entry_size) for i in range(count)]
    names = sections[names_index]
    strings = data[names[4] : names[4] + names[5]]
    result = {}
    for section in sections:
        name_offset, kind, flags, _, content_offset, size, _, _, alignment, _ = section
        if not flags & 2:
            continue
        name = strings[name_offset : strings.index(b"\0", name_offset)].decode()
        content = b"" if kind == 8 else data[content_offset : content_offset + size]
        if kind != 8 and len(content) != size:
            raise ValueError(f"truncated section {name}: {path}")
        result[name] = {
            "type": kind,
            "flags": flags,
            "alignment": alignment,
            "size": size,
            "sha256": hashlib.sha256(content).hexdigest(),
        }
    if not result:
        raise ValueError(f"no allocated sections: {path}")
    return result


class Reproduction:
    def __init__(self, args):
        self.args = args
        self.work = args.work_dir.resolve()
        self.source = (args.source_dir or self.work / "llama.cpp").resolve()
        self.baseline = (args.build_dir or self.work / "baseline").resolve()
        self.model = (args.model or self.work / "models" / MODEL_NAME).resolve()
        self.llvm = args.llvm_bin.resolve() if args.llvm_bin else None
        self.ir = self.work / "ir"
        self.variant = self.work / "variants/rewrite"
        self.control = self.work / "variants/control"
        self.prompt = HERE / "prompt.txt"
        self.work.mkdir(parents=True, exist_ok=True)
        self.logs = self.work / "logs"
        self.logs.mkdir(exist_ok=True)
        self.sequence = len(list(self.logs.glob("*.command.json")))
        self.environment = {**os.environ, **NATIVE_ENV}
        write_json(
            self.work / "paths.json",
            {
                "source": str(self.source),
                "baseline": str(self.baseline),
                "model": str(self.model),
                "llvm_bin": str(self.llvm) if self.llvm else None,
                "prompt": str(self.prompt),
                "driver_sha256": file_hash(Path(__file__)),
                "prompt_sha256": file_hash(self.prompt),
            },
        )

    def run(self, command, label, *, cwd=None, env=None, timeout=None, stdout_path=None, stderr_path=None):
        self.sequence += 1
        prefix = self.logs / f"{self.sequence:04d}-{label}"
        command = [str(value) for value in command]
        cwd = Path(cwd or PROJECT).resolve()
        record = {"command": command, "cwd": str(cwd), "environment_overrides": NATIVE_ENV | (env or {})}
        write_json(prefix.with_suffix(".command.json"), record)
        print(f"running {label}", flush=True)
        started = time.monotonic()
        raw = subprocess.run(
            command,
            cwd=cwd,
            env=self.environment | (env or {}),
            capture_output=True,
            timeout=timeout,
            check=False,
        )
        prefix.with_suffix(".stdout").write_bytes(raw.stdout)
        prefix.with_suffix(".stderr").write_bytes(raw.stderr)
        if stdout_path is not None:
            stdout_path.write_bytes(raw.stdout)
        if stderr_path is not None:
            stderr_path.write_bytes(raw.stderr)
        record.update({"returncode": raw.returncode, "elapsed_seconds": time.monotonic() - started})
        write_json(prefix.with_suffix(".command.json"), record)
        if raw.returncode:
            raise RuntimeError(f"{label} failed with exit {raw.returncode}; see {prefix}.stderr")
        return subprocess.CompletedProcess(
            command, raw.returncode, raw.stdout.decode(errors="replace"), raw.stderr.decode(errors="replace")
        )

    def verify_source(self):
        revision = self.run(["git", "-C", self.source, "rev-parse", "HEAD"], "source-revision").stdout.strip()
        dirty = self.run(
            ["git", "-C", self.source, "status", "--porcelain", "--untracked-files=no"], "source-clean"
        ).stdout
        if revision != REVISION or dirty:
            raise ValueError(f"source must be clean at pinned revision {REVISION}")
        return revision

    def verify_model(self):
        actual = file_hash(self.model)
        if actual != MODEL_SHA256:
            raise ValueError(f"model SHA256 mismatch: {actual}")
        return actual

    def prepare(self):
        if not self.source.exists():
            self.source.parent.mkdir(parents=True, exist_ok=True)
            self.run(["git", "init", self.source], "source-init")
            self.run(["git", "-C", self.source, "remote", "add", "origin", SOURCE_URL], "source-remote")
            self.run(["git", "-C", self.source, "fetch", "--depth", "1", "origin", REVISION], "source-fetch")
            self.run(["git", "-C", self.source, "checkout", "--detach", REVISION], "source-checkout")
        self.verify_source()
        if not self.model.exists():
            self.model.parent.mkdir(parents=True, exist_ok=True)
            temporary = self.model.with_suffix(self.model.suffix + ".partial")
            if temporary.exists():
                raise ValueError(f"unfinished download exists; inspect it before retrying: {temporary}")
            print(f"downloading pinned model to {self.model}", flush=True)
            with urllib.request.urlopen(MODEL_URL, timeout=120) as response, temporary.open("xb") as output:
                shutil.copyfileobj(response, output)
            if file_hash(temporary) != MODEL_SHA256:
                raise ValueError(f"downloaded model SHA256 mismatch; retained {temporary}")
            temporary.rename(self.model)
        write_json(
            self.work / "prepare.json",
            {
                "source_url": SOURCE_URL,
                "source_revision": REVISION,
                "model_url": MODEL_URL,
                "model_revision": MODEL_REVISION,
                "model_sha256": self.verify_model(),
            },
        )

    def verify_tools(self):
        if self.llvm is None:
            raise ValueError("--llvm-bin is required for this phase")
        versions = {}
        for name in ("clang", "clang++", "llc", "opt", "llvm-objdump"):
            tool = self.llvm / name
            version = self.run([tool, "--version"], "version-" + name.replace("+", "p")).stdout
            if "23.1.5" not in version:
                raise ValueError(f"expected LLVM 23.1.5: {tool}")
            versions[name] = {"path": str(tool), "sha256": file_hash(tool), "version": version}
        write_json(self.work / "llvm-tools.json", versions)

    def llvm_tool(self, name):
        if self.llvm is None:
            raise ValueError("--llvm-bin is required for this phase")
        return self.llvm / name

    def make_wrappers(self):
        directory = self.work / "toolchain"
        directory.mkdir(exist_ok=True)
        receipts = []
        for name in ("clang", "clang++"):
            found = shutil.which(name)
            if found is None:
                raise ValueError(f"missing {name}; activate the project's Nix dev shell")
            wrapper = Path(found)
            text = wrapper.read_text()
            matches = re.findall(r"^\s*compiler=(/nix/store/\S+/bin/clang(?:\+\+)?)$", text, re.MULTILINE)
            if len(matches) != 1 or "clang-wrapper-23.1.3" not in text:
                raise ValueError(f"expected the Nix Clang 23.1.3 wrapper: {wrapper}")
            replacement = str(self.llvm_tool(name))
            if re.fullmatch(r"[-A-Za-z0-9_./+]+", replacement) is None:
                raise ValueError(
                    "LLVM path must contain only shell-safe path characters for wrapper substitution"
                )
            output = directory / name
            output.write_text(text.replace(matches[0], replacement))
            output.chmod(wrapper.stat().st_mode | 0o111)
            receipts.append(
                {
                    "wrapper": str(wrapper),
                    "wrapper_sha256": file_hash(wrapper),
                    "old_compiler": matches[0],
                    "new_compiler": replacement,
                    "output": str(output),
                    "output_sha256": file_hash(output),
                }
            )
        write_json(directory / "receipt.json", receipts)
        return directory

    def build(self):
        self.verify_source()
        self.verify_tools()
        if not self.args.reuse_build:
            wrappers = self.make_wrappers()
            command = [
                "cmake",
                "-S",
                self.source,
                "-B",
                self.baseline,
                "-G",
                "Ninja",
                "-DCMAKE_BUILD_TYPE=Release",
                "-DCMAKE_EXPORT_COMPILE_COMMANDS=ON",
                "-DCMAKE_C_COMPILER=" + str(wrappers / "clang"),
                "-DCMAKE_CXX_COMPILER=" + str(wrappers / "clang++"),
                "-DCMAKE_C_FLAGS_RELEASE=-O3 -DNDEBUG -gline-tables-only",
                "-DCMAKE_CXX_FLAGS_RELEASE=-O3 -DNDEBUG -gline-tables-only",
                "-DBUILD_SHARED_LIBS=ON",
                "-DGGML_OPENMP=OFF",
                "-DGGML_ACCELERATE=OFF",
                "-DLLAMA_BUILD_COMMON=ON",
                "-DLLAMA_BUILD_TOOLS=ON",
                "-DLLAMA_BUILD_EXAMPLES=ON",
                "-DLLAMA_BUILD_TESTS=OFF",
                "-DLLAMA_CONNECT=OFF",
                "-DLLAMA_USE_PREBUILT_UI=OFF",
                *("-D" + option + "=ON" for option in ON),
                *("-D" + option + "=OFF" for option in OFF),
            ]
            self.run(command, "configure")
            self.run(
                ["cmake", "--build", self.baseline, "--target", "llama-completion", "--parallel", "4"],
                "build",
            )
        self.verify_build()

    def verify_build(self):
        self.verify_source()
        cache_path = self.baseline / "CMakeCache.txt"
        cache = {}
        for line in cache_path.read_text().splitlines():
            match = re.match(r"([^:#/][^:]*):[^=]+=(.*)$", line)
            if match:
                cache[match[1]] = match[2]
        if (
            cache.get("CMAKE_BUILD_TYPE") != "Release"
            or Path(cache["CMAKE_HOME_DIRECTORY"]).resolve() != self.source
        ):
            raise ValueError("baseline must be a Release build of the selected checkout")
        for option in ON:
            if cache.get(option) != "ON":
                raise ValueError(f"baseline requires {option}=ON")
        for option in OFF:
            if cache.get(option, "OFF") != "OFF":
                raise ValueError(f"baseline requires {option}=OFF")
        if cache.get("GGML_OPENMP_ENABLED", "OFF") != "OFF":
            raise ValueError("baseline OpenMP must be effectively disabled")
        if cache.get("GGML_AVAILABLE_BACKENDS") != "ggml-cpu":
            raise ValueError("baseline must contain only the CPU backend")
        for language in ("C", "CXX"):
            if cache.get(f"CMAKE_{language}_FLAGS_RELEASE") != "-O3 -DNDEBUG -gline-tables-only":
                raise ValueError(f"baseline {language} release flags differ")
        database_path = self.baseline / "compile_commands.json"
        entries = json.loads(database_path.read_text())
        matches = [entry for entry in entries if entry["file"].endswith("/arch/x86/quants.c")]
        if len(matches) != 1:
            raise ValueError("expected one x86 quants compile command")
        entry = matches[0]
        command = compilation_args(entry)
        for flag in (
            "-O3",
            "-DNDEBUG",
            "-gline-tables-only",
            "-DGGML_USE_CPU_REPACK",
            "-DGGML_USE_LLAMAFILE",
        ):
            if flag not in command:
                raise ValueError(f"quants compile command lacks {flag}")
        if any("OPENMP" in flag or "fopenmp" in flag for flag in command):
            raise ValueError("quants compile command enables OpenMP")
        trace = self.run([*command, "-###"], "effective-compiler", cwd=entry["directory"])
        lines = [shlex.split(line) for line in trace.stderr.splitlines() if '"-cc1"' in line]
        if len(lines) != 1:
            raise ValueError("could not inspect the actual compiler invocation")
        cc1 = lines[0]
        if Path(cc1[0]).resolve() != self.llvm_tool("clang").resolve():
            raise ValueError("baseline compiler does not invoke the selected LLVM binary")
        if cc1[cc1.index("-target-cpu") + 1] != "znver5" or "+avx512bw" not in cc1 or "+avx512vl" not in cc1:
            raise ValueError("baseline must target znver5 with AVX512BW/VL")
        if "-O3" not in cc1 or "-debug-info-kind=line-tables-only" not in cc1:
            raise ValueError("effective compiler optimization/debug settings differ")
        if "clang-wrapper-23.1.3" not in cc1[cc1.index("-resource-dir") + 1]:
            raise ValueError("baseline must retain the Nix Clang 23.1.3 resource headers")
        if "-fopenmp" in cc1 or "GGML_USE_OPENMP" in cc1:
            raise ValueError("effective compiler enables OpenMP")
        for path in (self.baseline / "bin/llama-completion", self.baseline / "bin/libggml-cpu.so.0"):
            if not path.is_file():
                raise ValueError(f"missing baseline output: {path}")
        write_json(
            self.work / "build-verification.json",
            {
                "source_revision": REVISION,
                "cache_sha256": file_hash(cache_path),
                "compile_database_sha256": file_hash(database_path),
                "quants_command": entry,
                "cc1": cc1,
                "baseline_library_sha256": file_hash(self.baseline / "bin/libggml-cpu.so.0"),
                "reused": self.args.reuse_build,
            },
        )
        return entry

    def relink(self, obj, output):
        output.mkdir(parents=True, exist_ok=True)
        recipes = self.run(["ninja", "-C", self.baseline, "-t", "commands", "ggml-cpu"], "link-recipe").stdout
        lines = [
            line for line in recipes.splitlines() if " -shared " in line and " -o bin/libggml-cpu.so." in line
        ]
        if len(lines) != 1:
            raise ValueError("expected one CPU shared-library link recipe")
        command = shlex.split(lines[0])
        if command[:2] != [":", "&&"] or command[-2:] != ["&&", ":"]:
            raise ValueError("unexpected Ninja link recipe wrapper")
        command = command[2:-2]
        if any(token in {"&&", ";", "||", "|"} for token in command):
            raise ValueError("unsupported shell operator inside link recipe")
        for index in range(len(command) - 2, -1, -1):
            if command[index] == "-Xlinker" and command[index + 1].startswith("--dependency-file="):
                command[index + 1] = "--dependency-file=" + str(output / "link.d")
        command[command.index("-o") + 1] = str(output / "libggml-cpu.so.0")
        indices = [i for i, token in enumerate(command) if token.endswith("/arch/x86/quants.c.o")]
        if len(indices) != 1:
            raise ValueError("link recipe must contain exactly one ordinary quants object")
        command[indices[0]] = str(obj)
        self.run(command, "link-" + output.name, cwd=self.baseline)
        write_json(
            output / "link.json",
            {
                "command": command,
                "cwd": str(self.baseline),
                "library_sha256": file_hash(output / "libggml-cpu.so.0"),
            },
        )

    def rewrite(self):
        self.verify_tools()
        entry = self.verify_build()
        self.ir.mkdir(exist_ok=True)
        source = self.ir / "quants-original.ll"
        target = self.ir / "quants-rewrite.ll"
        command = compilation_args(entry)
        original_object = (Path(entry["directory"]) / command[command.index("-o") + 1]).resolve()
        command[command.index("-o") + 1] = str(source)
        command.remove("-c")
        command += ["-S", "-emit-llvm", "-fno-discard-value-names", "-mllvm", "-preserve-ll-uselistorder"]
        self.run(command, "emit-quants", cwd=entry["directory"])
        self.run(
            [
                sys.executable,
                HERE / "rewrite.py",
                source,
                target,
                "--function",
                "ggml_vec_dot_q5_0_q8_0",
                "--expect-sites",
                "3",
                "--helpers-dir",
                self.ir,
            ],
            "rewrite-quants",
        )
        helper = self.ir / "q5_bitspread.ll"
        fixture = PROJECT / "tests/real/llama_q5_bitspread.ll"
        if helper.read_bytes() != fixture.read_bytes():
            raise ValueError("extracted helper differs from the committed proved fixture")
        for name, path in (("control", source), ("rewrite", target)):
            self.run([self.llvm_tool("opt"), "-passes=verify", "-disable-output", path], "verify-" + name)
            self.run(
                [
                    self.llvm_tool("llc"),
                    "-O3",
                    "-relocation-model=pic",
                    "-filetype=obj",
                    path,
                    "-o",
                    self.ir / (name + ".o"),
                ],
                "lower-" + name,
            )
        disassemblies = []
        for name, obj in (("ordinary", original_object), ("control", self.ir / "control.o")):
            result = self.run(
                [self.llvm_tool("llvm-objdump"), "-dr", "--no-show-raw-insn", obj], "disassemble-" + name
            )
            normalized = "\n".join(result.stdout.splitlines()[2:]) + "\n"
            (self.ir / (name + ".asm")).write_text(normalized)
            disassemblies.append(normalized)
        ordinary_sections = allocated_sections(original_object)
        control_sections = allocated_sections(self.ir / "control.o")
        if disassemblies[0] != disassemblies[1] or ordinary_sections != control_sections:
            raise ValueError("direct original-IR lowering differs from ordinary Clang object; see ir/*.asm")
        write_json(
            self.ir / "control-equality.json",
            {
                "disassembly_and_relocations_equal": True,
                "allocated_sections_equal": True,
                "sections": ordinary_sections,
                "ordinary_object": str(original_object),
                "ordinary_sha256": file_hash(original_object),
                "control_sha256": file_hash(self.ir / "control.o"),
            },
        )
        self.relink(self.ir / "control.o", self.control)
        self.relink(self.ir / "rewrite.o", self.variant)
        write_json(
            self.work / "rewrite.json",
            {
                "source_ir_sha256": file_hash(source),
                "target_ir_sha256": file_hash(target),
                "helper_sha256": file_hash(helper),
                "witness_sha256": file_hash(target.with_suffix(".ll.witness.json")),
                "control_library_sha256": file_hash(self.control / "libggml-cpu.so.0"),
                "target_library_sha256": file_hash(self.variant / "libggml-cpu.so.0"),
                "baseline_library_sha256": file_hash(self.baseline / "bin/libggml-cpu.so.0"),
                "replaced_objects": ["ggml-cpu/arch/x86/quants.c.o"],
            },
        )

    def verify_rewrite(self):
        receipt = json.loads((self.work / "rewrite.json").read_text())
        expected = {
            "source_ir_sha256": self.ir / "quants-original.ll",
            "target_ir_sha256": self.ir / "quants-rewrite.ll",
            "helper_sha256": self.ir / "q5_bitspread.ll",
            "witness_sha256": self.ir / "quants-rewrite.ll.witness.json",
            "control_library_sha256": self.control / "libggml-cpu.so.0",
            "target_library_sha256": self.variant / "libggml-cpu.so.0",
            "baseline_library_sha256": self.baseline / "bin/libggml-cpu.so.0",
        }
        for key, path in expected.items():
            if file_hash(path) != receipt[key]:
                raise ValueError(f"rewrite artifact changed: {path}")
        if (self.ir / "q5_bitspread.ll").read_bytes() != (
            PROJECT / "tests/real/llama_q5_bitspread.ll"
        ).read_bytes():
            raise ValueError("rewritten helper no longer matches the proved fixture")
        return receipt

    def new_run(self, name):
        root = self.work / name
        root.mkdir(exist_ok=True)
        for index in range(1, 1000000):
            path = root / f"{index:04d}"
            try:
                path.mkdir()
                return path
            except FileExistsError:
                continue
        raise RuntimeError("too many retained runs")

    def check(self):
        self.verify_tools()
        self.verify_build()
        rewrite = self.verify_rewrite()
        self.verify_model()
        self.run(["bash", PROJECT / "tests/llama-bitspread.sh", self.args.ir_lean.resolve()], "lean-proof")
        alive = self.run(
            [
                "alive-tv",
                "--bidirectional",
                "--disable-undef-input",
                "--smt-to=120000",
                self.ir / "q5_bitspread.ll",
            ],
            "alive-equivalence",
            timeout=300,
        )
        if (
            "These functions seem to be equivalent!" not in alive.stdout
            or "ERROR:" in alive.stdout + alive.stderr
        ):
            raise ValueError("Alive2 did not establish bidirectional equivalence")
        helper_obj = self.ir / "native-helper.o"
        self.run(
            [
                self.llvm_tool("llc"),
                "-O3",
                "-mcpu=znver5",
                "-filetype=obj",
                self.ir / "q5_bitspread.ll",
                "-o",
                helper_obj,
            ],
            "native-helper",
        )
        entry = json.loads((self.work / "build-verification.json").read_text())["quants_command"]
        native = self.work / "native-check"
        self.run(
            [
                compilation_args(entry)[0],
                "-O3",
                "-march=znver5",
                HERE / "native_check.c",
                helper_obj,
                "-o",
                native,
            ],
            "native-check-build",
        )
        self.run([native], "native-check")
        built = self.run(
            [
                sys.executable,
                HERE / "build_capture.py",
                "--source-dir",
                self.source,
                "--build-dir",
                self.baseline,
                "--output-dir",
                self.work / "capture",
            ],
            "capture-build",
        )
        binary = Path(json.loads(built.stdout)["binary"])
        output = self.new_run("correctness")
        config = argparse.Namespace(**vars(self.args))
        config.model, config.prompt = self.model, self.prompt
        command = measure.completion_command(config, binary)
        write_json(output / "command.json", command)
        reference = None
        comparisons = {}
        for name, library_dir in (
            ("baseline-a", self.baseline / "bin"),
            ("baseline-b", self.baseline / "bin"),
            ("target", self.variant),
        ):
            environment = {
                "LD_LIBRARY_PATH": str(library_dir) + ":" + str(self.baseline / "bin"),
                "LLAMA_EXACT_OUTPUT_PREFIX": str(output / name),
            }
            mapping = self.run(["ldd", binary], "loader-" + name, env=environment).stdout
            (output / (name + "-ldd.txt")).write_text(mapping)
            loaded = re.search(r"^\s*libggml-cpu\.so\.0 => (\S+) \(", mapping, re.MULTILINE)
            if loaded is None or Path(loaded[1]).resolve() != (library_dir / "libggml-cpu.so.0").resolve():
                raise ValueError(f"capture selected the wrong CPU library: {name}")
            self.run(
                command,
                "capture-" + name,
                env=environment,
                stdout_path=output / (name + ".txt"),
                stderr_path=output / (name + ".log"),
            )
            actual = (output / (name + ".txt")).read_bytes()
            if reference is not None and actual != reference:
                raise ValueError(f"generated text differs: {name}")
            reference = actual
            if name != "baseline-a":
                compared = self.run(
                    [sys.executable, HERE / "compare.py", output / "baseline-a", output / name],
                    "compare-" + name,
                )
                comparisons[name] = json.loads(compared.stdout)
                write_json(output / (name + "-comparison.json"), comparisons[name])
        write_json(
            output / "result.json",
            {"all_equal": True, "comparisons": comparisons, "model_sha256": MODEL_SHA256, "rewrite": rewrite},
        )
        write_json(
            self.work / "check.json",
            {
                "result": str(output / "result.json"),
                "result_sha256": file_hash(output / "result.json"),
                "settings": self.inference_settings(),
                "baseline_library_sha256": rewrite["baseline_library_sha256"],
                "target_library_sha256": rewrite["target_library_sha256"],
            },
        )

    def inference_settings(self):
        config = argparse.Namespace(**vars(self.args))
        config.model, config.prompt = self.model, self.prompt
        return {
            "threads": self.args.threads,
            "first_cpu": self.args.first_cpu,
            "tokens": self.args.tokens,
            "prompt_sha256": file_hash(self.prompt),
            "model_sha256": MODEL_SHA256,
            "sampling_seed": 1234,
            "stock_command": measure.completion_command(config, self.baseline / "bin/llama-completion"),
        }

    def bench(self):
        self.verify_tools()
        self.verify_build()
        rewrite = self.verify_rewrite()
        self.verify_model()
        checked = json.loads((self.work / "check.json").read_text())
        if (
            checked["target_library_sha256"] != rewrite["target_library_sha256"]
            or checked["baseline_library_sha256"] != rewrite["baseline_library_sha256"]
            or checked["settings"] != self.inference_settings()
            or file_hash(Path(checked["result"])) != checked["result_sha256"]
        ):
            raise ValueError("correctness evidence does not match this rewrite")
        output = self.new_run("measurements")
        output.rmdir()  # measure.py reserves its output directory itself.
        self.run(
            [
                sys.executable,
                HERE / "measure.py",
                "--build-dir",
                self.baseline,
                "--variant-dir",
                self.variant,
                "--model",
                self.model,
                "--prompt",
                self.prompt,
                "--output",
                output,
                "--threads",
                self.args.threads,
                "--first-cpu",
                self.args.first_cpu,
                "--tokens",
                self.args.tokens,
                "--pairs",
                self.args.pairs,
                "--seed",
                self.args.seed,
            ],
            "bench",
        )
        print(f"benchmark evidence: {output}", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=("prepare", "build", "rewrite", "check", "bench", "all"))
    parser.add_argument("--work-dir", type=Path, default=PROJECT / "build/llama-demo")
    parser.add_argument("--llvm-bin", type=Path)
    parser.add_argument("--source-dir", type=Path)
    parser.add_argument("--model", type=Path)
    parser.add_argument("--build-dir", type=Path)
    parser.add_argument("--reuse-build", action="store_true")
    parser.add_argument("--ir-lean", type=Path, default=PROJECT / "build/ir-lean")
    parser.add_argument("--threads", type=int, default=8)
    parser.add_argument("--first-cpu", type=int, default=8)
    parser.add_argument("--tokens", type=int, default=512)
    parser.add_argument("--pairs", type=int, default=12)
    parser.add_argument("--seed", type=int, default=20261107)
    args = parser.parse_args()
    if sys.platform != "linux":
        parser.error("this reproduction requires Linux ELF, taskset and shared CPU libraries")
    if args.phase != "prepare" and args.llvm_bin is None:
        parser.error("--llvm-bin is required for every phase except prepare")
    if min(args.threads, args.tokens, args.pairs) < 1 or args.first_cpu < 0:
        parser.error("threads, tokens and pairs must be positive; first-cpu must be nonnegative")
    if args.phase in {"check", "bench", "all"}:
        requested = set(range(args.first_cpu, args.first_cpu + args.threads))
        if not requested.issubset(os.sched_getaffinity(0)):
            parser.error("requested inference CPUs are outside the process affinity")
    try:
        reproduction = Reproduction(args)
        phases = ("prepare", "build", "rewrite", "check", "bench") if args.phase == "all" else (args.phase,)
        for phase in phases:
            print(f"phase: {phase}", flush=True)
            getattr(reproduction, phase)()
    except (OSError, ValueError, RuntimeError, KeyError, subprocess.TimeoutExpired) as error:
        print(f"reproduce: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
