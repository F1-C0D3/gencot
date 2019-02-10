COGENT_DB = /home/teege/cogent/cogent/.cabal-sandbox/x86_64-linux-ghc-8.4.3-packages.conf.d/
GENCOT_SRC = ../..

Output: Output.hs
	ghc -package-db $(COGENT_DB) -i$(GENCOT_SRC) --make -O $@.hs

Translate: Translate.hs
	ghc -package-db $(COGENT_DB) -i$(GENCOT_SRC) --make -O $@.hs

Ast: Ast.hs
	ghc -package-db $(COGENT_DB) -i$(GENCOT_SRC) --make -O $@.hs
