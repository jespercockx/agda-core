AGDA2HS = agda2hs
FLAGS =
LIBRARIES =

.PHONY: app alllib clean clean-lib clean-agdai

alllib: lib lib/Syntax.hs lib/Reduce.hs

# alllib: lib lib/*.hs

lib:
	mkdir lib

lib/%.hs: src/%.agda
	$(AGDA2HS) $(FLAGS) $(LIBRARIES) $< -o lib

clean: clean-lib clean-agdai

clean-lib:
	rm -rf lib

clean-agdai:
	rm src/*.agdai

app:
  cabal build
