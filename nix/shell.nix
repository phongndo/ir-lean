{ pkgs, proofPkgs }:
let
  llvmPackages = pkgs.llvmPackages_latest;
in
# The shell's compiler matches the LLVM headers, so pass plugins load in `opt`.
pkgs.mkShell.override { inherit (llvmPackages) stdenv; } {
  packages =
    with pkgs;
    [
      # Checks poison and UB behavior in tests/opcheck.py, which skips it if absent.
      alive2
      cmake
      # Provides lean and lake; lean-toolchain picks the version.
      elan
      hyperfine
      llvmPackages.clang-tools
      llvmPackages.lld
      llvmPackages.llvm
      ninja
      python3
      # ruff and ty come from uv.lock, so `uv run` is what picks their versions.
      uv

      # Formatters, linters and language servers for everything else in the repo.
      actionlint
      bash-language-server
      cmake-lint
      deadnix
      editorconfig-checker
      gersemi
      neocmakelsp
      nixd
      nixfmt
      rumdl
      shellcheck
      shfmt
      statix
      taplo
      yaml-language-server
      yamlfmt
    ]
    ++ lib.optionals stdenv.hostPlatform.isLinux [ perf ];
  # zlib is here for clangd, which looks for the headers of tests/real/zlib_harness.c.
  buildInputs = [
    llvmPackages.llvm
    pkgs.zlib
  ];
  # tests/proofs.sh proves theorems about this exact source.
  ZLIB_SRC = pkgs.zlib.src;
  # uv uses this Python instead of downloading its own.
  UV_PYTHON = "${pkgs.python3}/bin/python3";
  UV_PYTHON_DOWNLOADS = "never";
  # Python tools in this shell put their dependencies here, which isn't what uv's Python should see.
  shellHook = "unset PYTHONPATH";
  # The proofs follow the shape of the IR, which depends on the target and its headers, so every
  # host compiles them for this one target.
  PROOF_CFLAGS = toString [
    "--target=${proofPkgs.stdenv.hostPlatform.config}"
    "-isystem ${proofPkgs.glibc.dev}/include"
    "-isystem ${proofPkgs.linuxHeaders}/include"
    "-Wno-unused-command-line-argument"
  ];
  # The compiler wrapper warns about any target but the host's.
  NIX_CC_WRAPPER_SUPPRESS_TARGET_WARNING = 1;
}
