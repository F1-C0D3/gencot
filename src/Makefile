COGENT_DB = /home/teege/work/projekte/code/HoBit/software/cogent/cogent/.cabal-sandbox/x86_64-linux-ghc-8.6.3-packages.conf.d/
#COGENT_DB = /home/teege/cogent/cogent/.cabal-sandbox/x86_64-linux-ghc-8.4.3-packages.conf.d/
GENCOT_SRC = Gencot/Input.hs Gencot/Names.hs Gencot/Origin.hs \
	Gencot/Cogent/Ast.hs Gencot/Cogent/Output.hs Gencot/Cogent/Translate.hs \
	Gencot/C/Output.hs Gencot/C/Translate.hs Gencot/Util/Invocations.hs
EXPOSEPACKS = -package language-c -package cogent -package ansi-wl-pprint

gencot-translate: gencot-translate.hs $(GENCOT_SRC)
	ghc $(EXPOSEPACKS) --make -O $@.hs
# ghc -package-db $(COGENT_DB) --make -O $@.hs

gencot-exttypes: gencot-exttypes.hs $(GENCOT_SRC)
	ghc $(EXPOSEPACKS) --make -O $@.hs

gencot-extabs: gencot-extabs.hs $(GENCOT_SRC)
	ghc $(EXPOSEPACKS) --make -O $@.hs
