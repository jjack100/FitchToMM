{
  description = "A converter from Fitch-style natural deduction proofs to the Metamath format";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs?ref=nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
      in {
        packages.default = pkgs.haskellPackages.callCabal2nix "fitch-to-mm" self {};

        apps = {
          default = {
            type = "app";
            program = "${self.packages.${system}.default}/bin/fitch2mm";
          };
        };

        packages.schemas = pkgs.runCommand "fitch-to-mm-schemas" {} ''
          mkdir -p $out
          cp -r ${./schemas}/* $out/
        '';

        devShells.default = pkgs.mkShell {
          name = "fitch-to-mm-dev";
          buildInputs = with pkgs.haskellPackages; [
            # Haskell development tools
            cabal-gild
            cabal-install
            haskell-language-server
            ghc
            hlint
            zlib

            # Metamath tools
            pkgs.metamath
            pkgs.mmj2
          ];

          shellHook = ''
            echo "Entering devShell for FitchToMM (system: ${system})"
          '';
        };
      });
}
