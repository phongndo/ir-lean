{
  description = "A Lean backend for LLVM IR";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs =
    { nixpkgs, ... }:
    let
      systems = nixpkgs.lib.genAttrs [
        "aarch64-darwin"
        "x86_64-linux"
      ];
    in
    {
      formatter = systems (system: nixpkgs.legacyPackages.${system}.nixfmt);
      devShells = systems (
        system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
          llvmPackages = pkgs.llvmPackages_latest;
        in
        {
          # The shell's compiler matches the LLVM headers, so pass plugins load in `opt`.
          default = pkgs.mkShell.override { inherit (llvmPackages) stdenv; } {
            packages =
              with pkgs;
              [
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
              ++ lib.optionals stdenv.hostPlatform.isLinux [
                # Checks poison and UB behavior in tests/opcheck.py, which skips it if absent.
                alive2
                perf
              ];
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
          };
        }
      );
    };
}
