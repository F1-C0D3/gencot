all: build links

build: gcbin pmbin itbin acbin

GCBIN = gencot-bin
PMBIN = parmod-bin
ITBIN = items-bin
ACBIN = auxcog-bin

gcbin: 
	cabal new-build $(GCBIN)

pmbin: 
	cabal new-build $(PMBIN)

itbin: 
	cabal new-build $(ITBIN)

acbin: 
	cabal new-build $(ACBIN)

links: bin/$(GCBIN) bin/$(PMBIN) bin/$(ITBIN) bin/$(ACBIN)

bin/$(GCBIN):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(GCBIN)/build/$(GCBIN)/$(GCBIN) .)

bin/$(PMBIN):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(PMBIN)/build/$(PMBIN)/$(PMBIN) .)

bin/$(ITBIN):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(ITBIN)/build/$(ITBIN)/$(ITBIN) .)

bin/$(ACBIN):
	(cd bin; ln -s ../dist-newstyle/build/*/*/gencot-*/x/$(ACBIN)/build/$(ACBIN)/$(ACBIN) .)

