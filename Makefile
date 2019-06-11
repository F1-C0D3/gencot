all: build links

build:
	cabal new-build

CHECK = gencot-check
TRANS = gencot-translate
DECCM = gencot-deccomments
EXTFS = gencot-extfuns
PMGEN = parmod-gen
PMPRC = parmod-proc

links: bin/$(CHECK) bin/$(TRANS) bin/$(DECCM) bin/$(EXTFS) bin/$(PMGEN) bin/$(PMPRC)

bin/$(CHECK):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(CHECK)/build/$(CHECK)/$(CHECK) .)

bin/$(TRANS):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(TRANS)/build/$(TRANS)/$(TRANS) .)

bin/$(DECCM):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(DECCM)/build/$(DECCM)/$(DECCM) .)

bin/$(EXTFS):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(EXTFS)/build/$(EXTFS)/$(EXTFS) .)

bin/$(PMGEN):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(PMGEN)/build/$(PMGEN)/$(PMGEN) .)

bin/$(PMPRC):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(PMPRC)/build/$(PMPRC)/$(PMPRC) .)
