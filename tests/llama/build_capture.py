#!/usr/bin/env python3
"""Build the stock completion path with raw-logit capture, using an existing Linux shared build.

Run inside the project's dev shell. Only output-dir is written; llama.cpp and its baseline build are read.
The JSON on stdout names the binary and build receipt. Capture I/O makes this binary unsuitable for timing.
"""

import argparse
import json
import shlex
import shutil
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.append(str(HERE.parents[1] / "tools"))
from irlean import hashing, proc  # noqa: E402

EDITS = [
    ('#include "chat.h"', '#include "chat.h"\n#include "capture.h"'),
    (
        "    const llama_vocab * vocab = llama_model_get_vocab(model);",
        "    const llama_vocab * vocab = llama_model_get_vocab(model);\n    exact_capture capture(vocab);",
    ),
    ("    bool is_antiprompt = false;", "    capture.prompt(embd_inp);\n\n    bool is_antiprompt = false;"),
    (
        "            const llama_token id = common_sampler_sample(smpl, ctx, -1);",
        "            capture.before_sample(ctx, n_past);\n"
        "            const llama_token id = common_sampler_sample(smpl, ctx, -1);\n"
        "            capture.sampled(id);",
    ),
    ("    llama_backend_free();", "    capture.finish();\n\n    llama_backend_free();"),
]


def resolved(path, directory):
    return (directory / path).resolve()


def build(source_dir, build_dir, output_dir):
    source_dir, build_dir, output_dir = (path.resolve() for path in (source_dir, build_dir, output_dir))
    if output_dir == source_dir or source_dir in output_dir.parents:
        raise ValueError("output-dir must be outside the llama.cpp source checkout")
    source = source_dir / "tools/completion/completion.cpp"
    original = source.read_text()
    instrumented = original
    for before, after in EDITS:
        if instrumented.count(before) != 1:
            raise ValueError(f"expected one completion capture anchor: {before!r}")
        instrumented = instrumented.replace(before, after)

    database = json.loads((build_dir / "compile_commands.json").read_text())
    entries = [
        entry
        for entry in database
        if resolved(entry["file"], resolved(entry["directory"], build_dir)) == source
    ]
    if len(entries) != 1:
        raise ValueError(f"expected one compile command for {source}, found {len(entries)}")
    entry = entries[0]
    directory = resolved(entry["directory"], build_dir)
    compile_args = list(entry["arguments"]) if "arguments" in entry else shlex.split(entry["command"])
    inputs = [
        index
        for index, value in enumerate(compile_args)
        if not value.startswith("-") and resolved(value, directory) == source
    ]
    if len(inputs) != 1 or "-c" not in compile_args or "-o" not in compile_args:
        raise ValueError("completion compile command needs one source, -c and -o")

    libraries = build_dir / "bin"
    shared = [
        libraries / f"lib{name}.so" for name in ("llama-common", "llama", "ggml", "ggml-cpu", "ggml-base")
    ]
    archive = build_dir / "common/libllama-common-base.a"
    for path in [*shared, archive]:
        if not path.is_file():
            raise ValueError(f"missing baseline library: {path}")

    output_dir.mkdir(parents=True, exist_ok=True)
    copy = output_dir / "completion-capture.cpp"
    copy.write_text(instrumented)
    for name in ("capture.h", "capture_main.cpp"):
        shutil.copyfile(HERE / name, output_dir / name)
    obj = output_dir / "completion-capture.o"
    binary = output_dir / "llama-completion-exact"
    compile_args[compile_args.index("-o") + 1] = str(obj)
    compile_args[inputs[0]] = str(copy)
    compile_args += ["-I" + str(output_dir)]
    link_args = [
        compile_args[0],
        "-O3",
        "-DNDEBUG",
        "-gline-tables-only",
        str(obj),
        str(output_dir / "capture_main.cpp"),
        "-Wl,--enable-new-dtags",
        "-Wl,-rpath," + str(libraries),
        *(str(path) for path in shared),
        str(archive),
        "-o",
        str(binary),
    ]
    build_log = output_dir / "build.log"
    with build_log.open("w") as log:
        for command, cwd in ((compile_args, directory), (link_args, output_dir)):
            log.write(shlex.join(command) + "\n")
            log.flush()
            result = proc.run(command, cwd=cwd, stdout=log, stderr=proc.STDOUT)
            if result.exit:
                raise RuntimeError(f"capture build failed with exit {result.exit}; see {build_log}")

    receipt = output_dir / "capture-build.json"
    receipt.write_text(
        json.dumps(
            {
                "binary": str(binary),
                "binary_sha256": hashing.sha256_file(binary),
                "source": str(source),
                "source_sha256": hashing.sha256_file(source),
                "instrumented_source": str(copy),
                "instrumented_sha256": hashing.sha256_file(copy),
                "capture_sha256": hashing.sha256_file(output_dir / "capture.h"),
                "main_sha256": hashing.sha256_file(output_dir / "capture_main.cpp"),
                "compile_args": compile_args,
                "compile_cwd": str(directory),
                "link_args": link_args,
                "link_cwd": str(output_dir),
                "libraries": {str(path): hashing.sha256_file(path) for path in [*shared, archive]},
                "edits": EDITS,
                "log": str(build_log),
            },
            indent=2,
        )
        + "\n"
    )
    return {"binary": str(binary), "receipt": str(receipt)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-dir", required=True, type=Path)
    parser.add_argument("--build-dir", required=True, type=Path)
    parser.add_argument("--output-dir", required=True, type=Path)
    args = parser.parse_args()
    try:
        result = build(args.source_dir, args.build_dir, args.output_dir)
    except (OSError, ValueError, RuntimeError) as error:
        print(f"build_capture: {error}", file=sys.stderr)
        return 1
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
