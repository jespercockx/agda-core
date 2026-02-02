AGDA2HS = agda2hs
FLAGS =
LIBRARIES =

.PHONY: app alllib clean clean-lib clean-agdai nix-tc nix-build

# this should stay in sync with the modules defined in cabal
# also the order is silly, we redo a lot of the work because we don't know the dependencies
alllib: lib \
  lib/Agda/Core/Prelude.hs \
  lib/Agda/Core/GlobalScope.hs \
  lib/Agda/Core/Syntax/Strengthening.hs \
  lib/Agda/Core/Syntax/VarInTerm.hs \
  lib/Agda/Core/Syntax.hs \
  lib/Agda/Core/Reduce.hs \
  lib/Agda/Core/Rules/Conversion.hs \
  lib/Agda/Core/Rules/Typing.hs \
  lib/Agda/Core/TCM/TCM.hs \
  lib/Agda/Core/TCM/Instances.hs \
  lib/Agda/Core/Checkers/Converter.hs \
  lib/Agda/Core/Checkers/TypeCheck.hs \
  lib/Agda/Core/Checkers/Terminate.hs

# alllib: lib lib/*.hs

lib:
	mkdir lib

lib/%.hs: src/%.agda
	$(AGDA2HS) $(FLAGS) $(LIBRARIES) $< -o lib

clean: clean-lib clean-agdai

clean-lib:
	rm -rf lib

clean-agdai:
	find src -iname *.agdai -delete
	rm -rf _build

app: alllib
	cabal build

clean-hs:
	rm -rf dist-newstyle

nix/agda-core.nix: agda-core.cabal
	cd nix && cabal2nix ../. > ./agda-core.nix # generate agda-core.nix
	sed -i -e 's/}:/, agda2hs }:/1' ./nix/agda-core.nix # add a new argument `agda2hs` before the first occurence of `}:`
	patch ./nix/agda-core.nix ./nix/agda-core.diff # apply the rest of the diff

nix-tc:
	nix build .#agda-core-lib --print-build-logs

nix-build:
	nix build .#agda-core --print-build-logs
