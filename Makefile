all: build links

build: check deccm pmext pmgen pmprc # trans extfs

CHECK = gencot-check
TRANS = gencot-translate
DECCM = gencot-deccomments
EXTFS = gencot-extfuns
PMEXT = parmod-extfuns
PMGEN = parmod-gen
PMPRC = parmod-proc

check: 
	cabal new-build $(CHECK)

deccm: 
	cabal new-build $(DECCM)

pmext: 
	cabal new-build $(PMEXT)

pmgen: 
	cabal new-build $(PMGEN)

pmprc: 
	cabal new-build $(PMPRC)

trans: 
	cabal new-build $(TRANS)

extfs: 
	cabal new-build $(EXTFS)

links: bin/$(CHECK) bin/$(DECCM) bin/$(PMEXT) bin/$(PMGEN) bin/$(PMPRC) # bin/$(TRANS) bin/$(EXTFS) 

bin/$(CHECK):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(CHECK)/build/$(CHECK)/$(CHECK) .)

bin/$(TRANS):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(TRANS)/build/$(TRANS)/$(TRANS) .)

bin/$(DECCM):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(DECCM)/build/$(DECCM)/$(DECCM) .)

bin/$(EXTFS):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(EXTFS)/build/$(EXTFS)/$(EXTFS) .)

bin/$(PMEXT):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(PMEXT)/build/$(PMEXT)/$(PMEXT) .)

bin/$(PMGEN):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(PMGEN)/build/$(PMGEN)/$(PMGEN) .)

bin/$(PMPRC):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(PMPRC)/build/$(PMPRC)/$(PMPRC) .)
