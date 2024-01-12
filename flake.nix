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
    let
    in (flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        agdaDerivation = pkgs.callPackage ./nix/mkAgdaDerivation.nix {};
        agda2hslib = agdaDerivation
          { pname = "agda2hs";
            meta = {};
            version = "1.3";
            tcDir = "lib";
            src = agda2hs-src;
          };
        scopelib = agdaDerivation
          { pname = "scope";
            meta = {};
            version = "0.1.0.0";
            tcDir = "src";
            buildInputs = [
              agda2hslib
            ];
            src = scope-src;
          };
      in {
        packages = rec {
          agda-core = agdaDerivation
            { name = "agda-core";
              pname = "agda-core";
              meta = {};
              libraryName = "agda-core";
              libraryFile = "core.agda-lib";
              tcDir = "src";
              buildInputs = [ agda2hslib scopelib ];
              src = ./.;
            };
          default = agda-core;
        };

        devShells.default = pkgs.mkShell {
          # should also include agda2hs, but not building it for now
          packages = [ (pkgs.agda.withPackages [ agda2hslib scopelib ]) pkgs.haskell ];
        };
      }));
}
