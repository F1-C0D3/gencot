COGENT_DB = /home/teege/work/projekte/code/HoBit/software/cogent/cogent/.cabal-sandbox/x86_64-linux-ghc-8.6.3-packages.conf.d/
GENCOT_SRC = Gencot/Input.hs Gencot/Names.hs Gencot/Origin.hs \
	Gencot/Cogent/Ast.hs Gencot/Cogent/Output.hs Gencot/Cogent/Translate.hs \
	Gencot/C/Output.hs Gencot/C/Translate.hs
	
gencot-translate: gencot-translate.hs $(GENCOT_SRC)
	ghc -package-db $(COGENT_DB) --make -O $@.hs

