UNIT=all

HFILES = cards.h rank.h
CFILES = cards.c
UNITFILES = $(UNIT)-externs.cogent $(UNIT)-exttypes.cogent $(UNIT)-dvdtypes.cogent $(UNIT).cogent
ACFILES = $(UNIT)-externs.ac $(CFILES:.c=-entry.ac) $(UNIT)-gencot.ac
ACFILESPP = $(ACFILES:.ac=_pp.ac)
ACFILESINF = $(ACFILES:.ac=_pp_inferred.c)
ACFILESC = $(ACFILES:.ac=.c)
GENCOTFILES = $(UNIT)-gencot.h $(UNIT)-cogent-common.c 
OFILES = $(CFILES:.c=.o)
COGFILES = $(CFILES:.c=.cogent)
INCLFILES = $(HFILES:.h=-incl.cogent)
COGSRC = $(INCLFILES) $(COGFILES) $(UNITFILES)
COGHFILES = cogent-defns.h cogent-endianness.h
# Include path used for original and generated C program
INCLPATH = -I.

binary: cards
run: run-cards
cogent: $(COGSRC)
c: $(UNIT)-gen.c $(UNIT)-gen.h $(UNIT).c
cogent-binary: cogent-cards
cogent-run: run-cogent-cards

.PHONY: clean run-cards run-cogent-cards

STDGUM=$(shell cogent --libgum-dir)
GENCOTI=$(GENCOT_HOME)/include
GENCOTC=$(GENCOT_HOME)/c
COGPPARGS = --cogent-pp-args="-I$(GENCOTI)"
# The following is used to fix a problem of some cpp implementations
CPPFIX = --cpp-args='-x c $$CPPIN -o $$CPPOUT -P'

run-cards: cards
	./cards

$(UNIT)-external.items: $(UNIT).unit
ifeq ($(UNIT), all)
	items $(INCLPATH) used
else
	items $(INCLPATH) -u $(UNIT) used
endif

%-incl.cogent: %.h $(UNIT)-external.items
ifeq ($(UNIT), all)
	gencot hfile $*.h
else
	gencot -u $(UNIT) hfile $*.h
endif

# depends on $(INCLFILES) for comment transfer from declarations
%.cogent: %.c %.c-itemprops $(UNIT)-external.items $(INCLFILES)
ifeq ($(UNIT), all)
	gencot $(INCLPATH) cfile $*.c
else
	gencot $(INCLPATH) -u $(UNIT) cfile $*.c
endif

$(UNITFILES): $(UNIT).unit $(UNIT).unit-itemprops $(UNIT)-external.items $(CFILES) common.gencot-std
ifeq ($(UNIT), all)
	gencot $(INCLPATH) unit
else
	gencot $(INCLPATH) -u $(UNIT) unit
endif

$(UNIT)-gencot.ac:
	cp $(GENCOTC)/gencot.ac $(UNIT)-gencot.ac

$(UNIT)-gen.c $(UNIT)-gen.h $(ACFILESINF): $(COGSRC) $(ACFILES)
	cogent -o $(UNIT)-gen -g $(UNIT).cogent $(COGPPARGS) --infer-c-funcs="$(ACFILES)" $(CPPFIX)

$(UNIT).c $(ACFILESC) $(GENCOTFILES): $(UNIT)-gen.c $(UNIT)-gen.h $(ACFILESINF) $(UNIT).unit $(COGHFILES)
ifeq ($(UNIT), all)
	auxcog $(INCLPATH) unit
else
	auxcog $(INCLPATH) -u $(UNIT) unit
endif

cogent-cards: $(UNIT).c $(UNIT)-gen.c $(UNIT)-gen.h $(GENCOTFILES) $(ACFILESC) $(COGHFILES)
	cc -o cogent-cards $(INCLPATH) $(UNIT).c

run-cogent-cards: cogent-cards
	./cogent-cards

clean:
	-rm -f cards
	-rm -f $(COGSRC) $(UNIT)-external.items cards-entry.ac
	-rm -rf comments
	-rm -f $(UNIT)-gen.c $(UNIT)-gen.h $(ACFILESPP) $(ACFILESINF) $(UNIT)-gencot.ac
	-rm -f $(UNIT).c $(GENCOTFILES) $(ACFILESC)
	-rm -f cogent-cards
