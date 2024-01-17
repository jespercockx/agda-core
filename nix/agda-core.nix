# this package is produced by calling cabal2nix . in the parent directory
# and then doing the following:
# add an agda2hs argument
# change src to ../. instead of ./.
# add buildTools = [agda2hs];
# add preBuild = ''make alllib'';
# make ./nix/agda-core.nix might be able to do it for you
{ mkDerivation, Agda, base, bytestring, containers, directory
, filepath, lib, mtl, unordered-containers, agda2hs
}:
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
  executableHaskellDepends = [
    Agda base bytestring containers directory filepath mtl
    unordered-containers
  ];
  license = lib.licenses.unlicense;
  mainProgram = "agda-core";
}
