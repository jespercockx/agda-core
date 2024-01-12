{agdaPackages, lib}: args:
with lib.strings;
let
  getAttrOrDefault = atr: def: set:
    if builtins.hasAttr atr set then builtins.getAttr atr set else def;
in
agdaPackages.mkDerivation (args //
  (if # don't override if Everything.agda is present
     args ? everythingFile ||
     # don't override if there's an explicit buildPhase
     (getAttrOrDefault "buildPhase" null args != null) ||
     # do override if either tcFiles or tcDir is present
     ! (args ? tcFiles || args ? tcDir)
   then builtins.trace "not overriding" {}
   else
     {buildPhase =
        let ipaths = getAttrOrDefault "includePaths" [] args;
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
             find "${args.tcDir}" -type f -name "*.agda" -print0 | xargs -0 -n1 -t ${"agda" + iarg}
             runHook postBuild
             ''
      ;}))
