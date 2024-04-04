AGDA2HS = agda2hs
FLAGS =
LIBRARIES =

.PHONY: app alllib clean clean-lib clean-agdai nix-tc nix-build

alllib: lib lib/Agda/Core/Syntax.hs lib/Agda/Core/Reduce.hs lib/Agda/Core/Typechecker.hs \
  lib/Agda/Core/TCM.hs

# alllib: lib lib/*.hs

lib:
	mkdir lib

lib/%.hs: src/%.agda
	$(AGDA2HS) $(FLAGS) $(LIBRARIES) $< -o lib

clean: clean-lib clean-agdai

clean-lib:
	rm -rf lib

clean-agdai:
	rm -rf src/*.agdai _build

app: alllib
	cabal build

nix/agda-core.nix: agda-core.cabal
	cd nix && cabal2nix ../. > ./agda-core.nix # generate agda-core.nix
	sed -i -e 's/ }:/\n, agda2hs }:/1' ./nix/agda-core.nix # replace first occurence of }: with an addition of a new argument -- agda2hs
	patch ./nix/agda-core.nix ./nix/agda-core.diff # apply the rest of the diff

nix-tc:
	nix build .#agda-core-lib --print-build-logs

nix-build:
	nix build .#agda-core --print-build-logs
