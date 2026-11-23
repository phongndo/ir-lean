{
  description = "A Lean backend for LLVM IR";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs =
    { self, nixpkgs, ... }:
    let
      forAllSystems =
        f: nixpkgs.lib.genAttrs (import ./nix/systems.nix) (system: f nixpkgs.legacyPackages.${system});
    in
    {
      formatter = forAllSystems (pkgs: pkgs.nixfmt);
      # The kernel corpus's builds, documented in docs/kernels.md.
      # The corpus is measured on x86-64 Linux.
      legacyPackages.x86_64-linux.kernels = import ./bench/kernels/variants.nix {
        pkgs = nixpkgs.legacyPackages.x86_64-linux;
        repo = self;
      };
      devShells = forAllSystems (
        pkgs:
        let
          default = import ./nix/shell.nix {
            inherit pkgs;
            proofPkgs = nixpkgs.legacyPackages.x86_64-linux;
          };
        in
        {
          inherit default;
          # The default shell, and llama.cpp's source, for tests/llama.py and tests/llama_bench.py.
          llama = default.overrideAttrs { LLAMA_CPP_SRC = pkgs.callPackage ./nix/llama.nix { }; };
        }
      );
    };
}
