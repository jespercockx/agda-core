AGDA2HS = agda2hs
FLAGS =
LIBRARIES =

.PHONY: app lib clean clean-lib clean-agdai clean-hs nix-tc nix-build

lib: src/Agda/Core.agda
	mkdir lib
	$(AGDA2HS) $(FLAGS) $(LIBRARIES) $< -o lib

clean: clean-lib clean-agdai clean-hs

clean-lib:
	rm -rf lib

clean-agdai:
	find src -iname '*.agdai' -delete
	rm -rf _build

clean-hs:
	find src -iname '*.hs' -delete
	rm -rf dist-newstyle

app: lib
	cabal build

nix/agda-core.nix: agda-core.cabal
	cd nix && cabal2nix ../. > ./agda-core.nix # generate agda-core.nix
	sed -i -e 's/}:/, agda2hs }:/1' ./nix/agda-core.nix # add a new argument `agda2hs` before the first occurence of `}:`
	patch ./nix/agda-core.nix ./nix/agda-core.diff # apply the rest of the diff

nix-tc:
	nix build .#agda-core-lib --print-build-logs

nix-build:
	nix build .#agda-core --print-build-logs
