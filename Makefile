all: build links

build: check deccm extfi pmgen pmprc # trans extfs

CHECK = gencot-check
TRANS = gencot-translate
DECCM = gencot-deccomments
EXTFS = gencot-extfuns
EXTFI = gencot-extfunids
PMGEN = parmod-gen
PMPRC = parmod-proc

check: 
	cabal new-build $(CHECK)

deccm: 
	cabal new-build $(DECCM)

extfi: 
	cabal new-build $(EXTFI)

pmgen: 
	cabal new-build $(PMGEN)

pmprc: 
	cabal new-build $(PMPRC)

trans: 
	cabal new-build $(TRANS)

extfs: 
	cabal new-build $(EXTFS)

links: bin/$(CHECK) bin/$(DECCM) bin/$(EXTFI) bin/$(PMGEN) bin/$(PMPRC) # bin/$(TRANS) bin/$(EXTFS) 

bin/$(CHECK):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(CHECK)/build/$(CHECK)/$(CHECK) .)

bin/$(TRANS):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(TRANS)/build/$(TRANS)/$(TRANS) .)

bin/$(DECCM):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(DECCM)/build/$(DECCM)/$(DECCM) .)

bin/$(EXTFS):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(EXTFS)/build/$(EXTFS)/$(EXTFS) .)

bin/$(EXTFI):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(EXTFI)/build/$(EXTFI)/$(EXTFI) .)

bin/$(PMGEN):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(PMGEN)/build/$(PMGEN)/$(PMGEN) .)

bin/$(PMPRC):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(PMPRC)/build/$(PMPRC)/$(PMPRC) .)
