{
  description = "Agda core";

  inputs.nixpkgs.url = github:NixOS/nixpkgs;
  inputs.flake-utils.url = github:numtide/flake-utils;
  inputs.agda2hs = {
    url = "github:agda/agda2hs";
    inputs.nixpkgs.follows = "nixpkgs";
    inputs.flake-utils.follows = "flake-utils";
  };
  inputs.scope = {
    url = "github:jespercockx/scope";
    inputs.nixpkgs.follows = "nixpkgs";
    inputs.agda2hs.follows = "agda2hs";
    inputs.flake-utils.follows = "flake-utils";
   };

  outputs = {self, nixpkgs, flake-utils, agda2hs, scope}:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {inherit system;};

        agda2hs-lib = agda2hs.packages.${system}.base-lib;
        scope-lib = scope.packages.${system}.scope-lib;
        agda2hs-custom = (agda2hs.lib.${system}.withPackages) [agda2hs-lib scope-lib];

        agda-core-pkg = import ./nix/agda-core.nix;
        agda-core = pkgs.haskellPackages.callPackage ./nix/agda-core.nix {agda2hs = agda2hs-custom;};
      in {
        packages = {
          inherit agda-core;
          agda-core-lib = pkgs.agdaPackages.mkDerivation
            { name = "agda-core-lib";
              pname = "agda-core-lib";
              meta = {};
              libraryName = "agda-core";
              libraryFile = "core.agda-lib";
              preBuild = ''
                echo "module Everything where" > Everything.agda
                find src -name '*.agda' | sed -e 's/src\///;s/\//./g;s/\.agda$//;s/^/import /' >> Everything.agda
              '';
              buildInputs = [ agda2hs-lib scope-lib ];
              src = ./.;
            };
          agda-core-hs = agda-core;
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
            # ^ this gets shadowed by the agda introduced as a dependency for agda-core
            #   still useful as you can look up the libraries file from the output
          ];
        };
      });
}
