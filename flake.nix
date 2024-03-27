{
  description = "Agda core";

  inputs.nixpkgs.url = github:NixOS/nixpkgs/eabe8d3eface69f5bb16c18f8662a702f50c20d5;
  inputs.flake-utils.url = github:numtide/flake-utils;
  inputs.mkAgdaDerivation.url = github:liesnikov/mkAgdaDerivation;
  inputs.agda2hs = {
    url = "github:liesnikov/agda2hs";
    inputs.nixpkgs.follows = "nixpkgs";
    inputs.mkAgdaDerivation.follows = "mkAgdaDerivation";
  };
  inputs.scope = {
    url = "github:liesnikov/scope";
    inputs.nixpkgs.follows = "nixpkgs";
    inputs.mkAgdaDerivation.follows = "mkAgdaDerivation";
    inputs.agda2hs.follows = "agda2hs";
   };

  outputs = {self, nixpkgs, flake-utils, mkAgdaDerivation, agda2hs, scope}:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {inherit system;};
        agdaDerivation = pkgs.callPackage mkAgdaDerivation.lib.mkAgdaDerivation {};
        agda2hs-lib = agda2hs.packages.${system}.agda2hs-lib;
        scope-lib = scope.packages.${system}.scope-lib;

        helper = agda2hs.lib.${system};
        hpkgs = pkgs.haskell.packages.ghc96;
        agda2hs-ghc96 = pkgs.callPackage (helper.agda2hs-expr) {
          inherit self;
          agda2hs = hpkgs.callPackage (helper.agda2hs-pkg "--jailbreak") {};
          inherit (hpkgs) ghcWithPackages;
        };
        agda2hs-custom = agda2hs-ghc96.withPackages [agda2hs-lib scope-lib];
        agda-core-pkg = import ./nix/agda-core.nix;
        agda-core = pkgs.haskellPackages.callPackage ./nix/agda-core.nix {agda2hs = agda2hs-custom;};
      in {
        packages = {
          agda-core-lib = agdaDerivation
            { name = "agda-core-lib";
              pname = "agda-core-lib";
              meta = {};
              libraryName = "agda-core";
              libraryFile = "core.agda-lib";
              tcDir = "src"; # typecheck all files in the src directory
              buildInputs = [ agda2hs-lib scope-lib ];
              src = ./.;
            };
          agda-core = agda-core;
          default = agda-core;
        };
        lib = {
          inherit agda-core-pkg;
        };

        devShells.default = pkgs.haskellPackages.shellFor {
          packages = p: [agda-core];
          buildInputs = with pkgs.haskellPackages; [
            cabal-install
            cabal2nix
            haskell-language-server
            agda2hs-custom
            (pkgs.agda.withPackages [ agda2hs-lib scope-lib ])
          ];
        };
      });
}
