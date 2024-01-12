{
  description = "Agda core";

  inputs.nixpkgs.url = github:NixOS/nixpkgs;
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
      getAttrOrDefault = atr: def: set:
        if builtins.hasAttr atr set then builtins.getAttr atr set else def;
    in (flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        agdaDerivation = args:
          pkgs.agdaPackages.mkDerivation
            (args // (if # don't override if Everything is present
                         args ? everythingFile ||
                         # don't override if there's an explicit buildPhase
                         (getAttrOrDefault "buildPhase" null args != null) ||
                         # do override if either tcFiles or tcDir is present
                         ! (args ? tcFiles || args ? tcDir)
                      then builtins.trace "not overriding" {}
                      else
                        {buildPhase =
                           let ipaths = getAttrOrDefault "includePaths" [] args;
                               concatMapStrings = pkgs.lib.strings.concatMapStrings;
                               iarg = concatMapStrings (path: "-i" + path + " ") ipaths;
                           in if args ? tcFiles
                              then
                                ''
                                runHook preBuild
                                ${concatMapStrings (f: "agda " + iarg + f + ";") args.tcFiles}
                                runHook postBuild
                                ''
                              else
                                ''
                                runHook preBuild
                                find "${args.tcDir}" -type f -name "*.agda" -print0 | xargs -0 -n1 ${"agda" + iarg}
                                runHook postBuild
                                ''
                         ;}));
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
        packages = {
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
        };

        defaultPackage = self.packages.${system}.agda-core;
      }));
}
