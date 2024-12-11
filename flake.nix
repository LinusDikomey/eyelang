{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs = {
        nixpkgs.follows = "nixpkgs";
      };
    };
  };
  outputs = { self, nixpkgs, flake-utils, rust-overlay }:
    flake-utils.lib.eachDefaultSystem(system:
      let
        overlays = [ (import rust-overlay) ];
        name = "eye";
        src = ./.;
        pkgs = import nixpkgs {
          inherit system overlays;
        };
      in
      {
        devShells.default = with pkgs; mkShell {
          nativeBuildInputs = [
            python3
            rust-bin.stable.latest.default
            llvmPackages_19.llvm
            libxml2
          ];
        };
      }
    );
}
