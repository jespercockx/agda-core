# this package is produced by calling cabal2nix . in the parent directory
# and then doing the following:
# add an agda2hs argument
# change src to ../. instead of ./.
# add buildTools = [agda2hs];
# add preBuild = ''make lib'';
# make ./nix/agda-core.nix might be able to do it for you
{ mkDerivation, Agda, ansi-terminal, base, bytestring, containers
, deepseq, directory, filepath, lib, mtl, transformers
, unordered-containers, agda2hs
}:
mkDerivation {
  pname = "agda-core";
  version = "0.1.0.0";
  src = ../.;
  buildTools = [agda2hs];
  preBuild = ''
    make lib
  '';
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [ base ];
  executableHaskellDepends = [
    Agda ansi-terminal base bytestring containers deepseq directory
    filepath mtl transformers unordered-containers
  ];
  license = lib.licenses.unlicense;
  mainProgram = "agda-core";
}
