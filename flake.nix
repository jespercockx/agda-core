{
  description = "Agda core";

  inputs.nixpkgs.url = github:NixOS/nixpkgs;
  inputs.flake-utils.url = github:numtide/flake-utils;
  inputs.agda2hs-src = {
     type = "github";
     owner = "liesnikov";
     repo = "agda2hs";
     rev = "9957295e9c0447e24fd73465a38e80dd75f74562";
     flake = false;
  };

  inputs.scope-src = {
     type = "github";
     owner = "liesnikov";
     repo = "scope";
     rev = "5890c20e26b0ce9cf9d31c9d3ec39f71ddebd236";
     flake = false;
   };

  outputs = {self, nixpkgs, flake-utils, agda2hs-src, scope-src}:
    let
    in (flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; overlays = []; };
        agda2hslib = pkgs.agdaPackages.mkDerivation
          { name = "agda2hslib";
            pname = "agda2hs";
            meta = {};
            version = "1.3";
            everythingFile = "lib/Haskell/Everything.agda";
            src = agda2hs-src;
          };
        scopelib = pkgs.agdaPackages.mkDerivation
          { name = "scopelib";
            pname = "scope";
            meta = {};
            version = "0.1.0.0";
            src = scope-src;
            everythingFile = "src/Everything.agda";
            buildInputs = [
              agda2hslib
            ];
          };
      in {
        packages = {
          agda-core = pkgs.agdaPackages.mkDerivation
            { name = "agda-core";
              pname = "agda-core";
              meta = {};
              libraryName = "agda-core";
              libraryFile = "core.agda-lib";
              everythingFile = "src/Typechecker.agda";
              buildInputs = [ agda2hslib scopelib ];
              src = ./.;
            };
        };

        defaultPackage = self.packages.${system}.agda-core;
      }));
}
