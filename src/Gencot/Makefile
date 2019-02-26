COGENT_DB = /home/teege/cogent/cogent/.cabal-sandbox/x86_64-linux-ghc-8.4.3-packages.conf.d/
GENCOT_SRC = ..

Origin: Origin.hs
	ghc -package-db $(COGENT_DB) --make -O $@.hs

Names: Names.hs
	ghc -package-db $(COGENT_DB) --make -O $@.hs

Input: Input.hs
	ghc -package-db $(COGENT_DB) --make -O $@.hs

Traversal: Traversal.hs
	ghc -package-db $(COGENT_DB) -i$(GENCOT_SRC) --make -O $@.hs

