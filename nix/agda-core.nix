{ mkDerivation, base, lib, agda2hs}:
mkDerivation {
  pname = "agda-core";
  version = "0.1.0.0";
  src = ./.;
  isLibrary = true;
  isExecutable = true;
  extraBuildInputs = [agda2hs];
  preBuild = ''
    ls -al
  '';
  libraryHaskellDepends = [ base ];
  executableHaskellDepends = [ base ];
  license = lib.licenses.unlicense;
  mainProgram = "agda-core";
}
