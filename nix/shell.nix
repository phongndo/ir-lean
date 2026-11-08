{ pkgs, proofPkgs }:
let
  llvmPackages = pkgs.llvmPackages_latest;
  # Alive2's releases trail LLVM, and nixpkgs builds it on an older LLVM than the one this shell has.
  # This is the upstream commit that builds on LLVM 23, so tests/opcheck.py reads IR the way clang
  # writes it. Moving llvmPackages_latest to another LLVM needs another commit here.
  alive2 =
    (pkgs.alive2.override {
      inherit (llvmPackages) llvm;
      clangStdenv = llvmPackages.stdenv;
    }).overrideAttrs
      {
        version = "21.0-unstable-2026-07-23";
        src = pkgs.fetchFromGitHub {
          owner = "AliveToolkit";
          repo = "alive2";
          rev = "a68009c9e81575bdcc249d3cc534514a76112221";
          hash = "sha256-Aaktd78j9lwcme8HS6+Ex1vL9++V71q2vt1hYMVMsCI=";
        };
      };
in
# The shell's compiler matches the LLVM headers, so pass plugins load in `opt`.
pkgs.mkShell.override { inherit (llvmPackages) stdenv; } {
  packages =
    with pkgs;
    [
      # Checks poison and UB behavior in tests/opcheck.py, which fails if it's absent.
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
  # tests/llvm.py proves theorems about this exact source: the monorepo at the tag this shell's clang was built from.
  LLVM_PROJECT_SRC = llvmPackages.llvm.monorepoSrc;
  # tests/llama.py proves a rewrite of this exact llama.cpp release correct.
  LLAMA_CPP_SRC = pkgs.fetchFromGitHub {
    owner = "ggml-org";
    repo = "llama.cpp";
    rev = "b12189";
    hash = "sha256-Y57pW8G1grsd6QD+mIQ7F7b2S5bwWdSlH39eRRYr0b0=";
  };
  # uv uses this Python instead of downloading its own.
  UV_PYTHON = "${pkgs.python3}/bin/python3";
  UV_PYTHON_DOWNLOADS = "never";
  # Python tools in this shell put their dependencies here, which isn't what uv's Python should see.
  # Tests and Lean processes at once: every core, unless memory runs out first, as a Lean process can take 3 GB.
  shellHook = ''
    unset PYTHONPATH
    if [ "$(uname)" = Darwin ]; then
      memory=$(sysctl -n hw.memsize)
    else
      memory=$(( $(getconf _PHYS_PAGES) * $(getconf PAGESIZE) ))
    fi
    jobs=$(( memory / 3000000000 ))
    [ "$(nproc)" -lt "$jobs" ] && jobs=$(nproc)
    [ "$jobs" -ge 1 ] || jobs=1
    export LEAN_JOBS=''${LEAN_JOBS:-$jobs}
    export CTEST_PARALLEL_LEVEL=''${CTEST_PARALLEL_LEVEL:-$jobs}
  '';
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
