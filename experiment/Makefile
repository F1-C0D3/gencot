COGENT_DB = /home/teege/cogent/cogent/.cabal-sandbox/x86_64-linux-ghc-8.4.3-packages.conf.d/
GENCOT_SRC = ../src

myDumpAst: myDumpAst.hs
	ghc -package language-c-0.8.3 --make -O myDumpAst.hs

myPrettyAst: myPrettyAst.hs
	ghc -package language-c-0.8.3 --make -O myPrettyAst.hs

myPrettySem: myPrettySem.hs
	ghc -package language-c-0.8.3 --make -O myPrettySem.hs

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

prettyAsAquote: prettyAsAquote.hs $(GENCOT_SRC)/Gencot/C/Translate.hs
	ghc -package-db $(COGENT_DB) -i$(GENCOT_SRC) --make -O $@.hs

prettyAsGencot: prettyAsGencot.hs $(GENCOT_SRC)/Gencot/C/Translate.hs $(GENCOT_SRC)/Gencot/C/Ast.hs $(GENCOT_SRC)/Gencot/C/Output.hs
	ghc -package-db $(COGENT_DB) -i$(GENCOT_SRC) --make -O $@.hs
