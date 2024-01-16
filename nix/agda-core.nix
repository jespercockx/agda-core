# this package is produced by calling cabal2nix . in the parent directory
# and then doing the following:
# add an agda2hs argument
# change src to ../. instead of ./.
# add buildTools = [agda2hs];
# add preBuild = ''make alllib'';
# maybe there's a better way to do it automatically, but I can't see it immediately
{ mkDerivation, base, lib, agda2hs}:
mkDerivation {
  pname = "agda-core";
  version = "0.1.0.0";
  src = ../.;
  isLibrary = true;
  isExecutable = true;
  buildTools = [agda2hs];
  preBuild = ''
    make alllib
  '';
  libraryHaskellDepends = [ base ];
  executableHaskellDepends = [ base ];
  license = lib.licenses.unlicense;
  mainProgram = "agda-core";
}
