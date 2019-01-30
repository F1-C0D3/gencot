COGENT_DB = /home/teege/cogent/cogent/.cabal-sandbox/x86_64-linux-ghc-8.4.3-packages.conf.d/
GENCOT_SRC = ../src

procSem1: procSem1.hs
	ghc -package-db $(COGENT_DB) --make -O $@.hs

procSem2: procSem2.hs
	ghc -package-db $(COGENT_DB) --make -O $@.hs

prettyCogNode1: prettyCogNode1.hs
	ghc -package-db $(COGENT_DB) --make -O $@.hs

prettyCogNode2: prettyCogNode2.hs
	ghc -package-db $(COGENT_DB) --make -O $@.hs

transToCog1: transToCog1.hs
	ghc -package-db $(COGENT_DB) -i$(GENCOT_SRC) --make -O $@.hs
