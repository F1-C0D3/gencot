COGENT_DB = /home/teege/cogent/cogent/.cabal-sandbox/x86_64-linux-ghc-8.4.3-packages.conf.d/
GENCOT_SRC = ../..
EXPOSEPACKS = -package language-c

Invocations: Invocations.hs
	ghc $(EXPOSEPACKS) -i$(GENCOT_SRC) --make -O $@.hs

Ident: Ident.hs
	ghc $(EXPOSEPACKS) -i$(GENCOT_SRC) --make -O $@.hs


