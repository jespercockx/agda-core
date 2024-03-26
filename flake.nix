{
  description = "Agda core";

  inputs.nixpkgs.url = github:NixOS/nixpkgs/eabe8d3eface69f5bb16c18f8662a702f50c20d5;
  inputs.flake-utils.url = github:numtide/flake-utils;
  inputs.agda2hs-src = {
     type = "github";
     owner = "agda";
     repo = "agda2hs";
     flake = false;
  };

  inputs.scope-src = {
     type = "github";
     owner = "jespercockx";
     repo = "scope";
     flake = false;
   };

  outputs = {self, nixpkgs, flake-utils, agda2hs-src, scope-src}:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {inherit system;};
        haskellPackages = pkgs.haskell.packages.ghc96;
        agda2hs-hs = haskellPackages.callCabal2nixWithOptions "agda2hs" agda2hs-src "--jailbreak" {};
        agdaDerivation = pkgs.callPackage ./nix/mkAgdaDerivation.nix {};
        agda2hs = pkgs.callPackage ./nix/agda2hs.nix {
          inherit self;
          agda2hs = agda2hs-hs;
          inherit (haskellPackages) ghcWithPackages;
        };
        agda2hs-lib = agdaDerivation
          { pname = "agda2hs";
            meta = {};
            version = "1.3";
            tcDir = "lib";
            src = agda2hs-src;
          };
        scope-lib = agdaDerivation
          { pname = "scope";
            meta = {};
            version = "0.1.0.0";
            tcDir = "src";
            buildInputs = [
              agda2hs-lib
            ];
            src = scope-src;
          };
        agda2hs-custom = agda2hs.withPackages [agda2hs-lib scope-lib];
        agda-core = haskellPackages.callPackage ./nix/agda-core.nix {agda2hs = agda2hs-custom;};
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

        devShells.default = haskellPackages.shellFor {
          packages = p: [agda-core];
          buildInputs = with haskellPackages; [
            cabal-install
            cabal2nix
            haskell-language-server
            agda2hs-custom
            (pkgs.agda.withPackages [ agda2hs-lib scope-lib ])
          ];
        };
      });
}
