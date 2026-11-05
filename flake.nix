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
                nixd
                nixfmt
                (python3.withPackages (p: [ p.pyyaml ]))
              ]
              ++ lib.optionals stdenv.hostPlatform.isLinux [
                # Checks poison and UB behavior in tests/opcheck.py, which skips it if absent.
                alive2
                perf
              ];
            buildInputs = [ llvmPackages.llvm ];
          };
        }
      );
    };
}
