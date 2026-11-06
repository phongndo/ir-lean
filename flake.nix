{
  description = "A Lean backend for LLVM IR";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs =
    { nixpkgs, ... }:
    let
      forAllSystems =
        f: nixpkgs.lib.genAttrs (import ./nix/systems.nix) (system: f nixpkgs.legacyPackages.${system});
    in
    {
      formatter = forAllSystems (pkgs: pkgs.nixfmt);
      devShells = forAllSystems (pkgs: {
        default = import ./nix/shell.nix {
          inherit pkgs;
          proofPkgs = nixpkgs.legacyPackages.x86_64-linux;
        };
      });
    };
}
