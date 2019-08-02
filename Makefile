all: build links

build: check deccm pmext pmgen pmprc trans extfs exttp

CHECK = gencot-check
TRANS = gencot-translate
DECCM = gencot-deccomments
EXTFS = gencot-extfuns
EXTTP = gencot-exttypes
PMEXT = parmod-extfuns
PMGEN = parmod-gen
PMPRC = parmod-proc

check: 
	cabal new-build $(CHECK)

trans: 
	cabal new-build $(TRANS)

deccm: 
	cabal new-build $(DECCM)

extfs: 
	cabal new-build $(EXTFS)

exttp: 
	cabal new-build $(EXTTP)

pmext: 
	cabal new-build $(PMEXT)

pmgen: 
	cabal new-build $(PMGEN)

pmprc: 
	cabal new-build $(PMPRC)

links: bin/$(CHECK) bin/$(DECCM) bin/$(PMEXT) bin/$(PMGEN) bin/$(PMPRC) bin/$(TRANS) bin/$(EXTFS)  bin/$(EXTTP)

bin/$(CHECK):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(CHECK)/build/$(CHECK)/$(CHECK) .)

bin/$(TRANS):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(TRANS)/build/$(TRANS)/$(TRANS) .)

bin/$(DECCM):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(DECCM)/build/$(DECCM)/$(DECCM) .)

bin/$(EXTFS):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(EXTFS)/build/$(EXTFS)/$(EXTFS) .)

bin/$(EXTTP):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(EXTTP)/build/$(EXTTP)/$(EXTTP) .)

bin/$(PMEXT):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(PMEXT)/build/$(PMEXT)/$(PMEXT) .)

bin/$(PMGEN):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(PMGEN)/build/$(PMGEN)/$(PMGEN) .)

bin/$(PMPRC):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(PMPRC)/build/$(PMPRC)/$(PMPRC) .)
