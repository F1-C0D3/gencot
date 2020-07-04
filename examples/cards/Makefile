UNIT=all

HFILES = cards.h rank.h
CFILES = cards.c
UNITFILES = $(UNIT)-externs.cogent $(UNIT)-exttypes.cogent $(UNIT)-dvdtypes.cogent $(UNIT).cogent
EDITFILES = ed-cards.done
ACFILES = $(UNIT)-externs.ac $(CFILES:.c=-entry.ac)
ACFILESPP = $(ACFILES:.ac=_pp.ac)
ACFILESINF = $(ACFILES:.ac=_pp_inferred.c)
ACFILESC = $(ACFILES:.ac=.c)
OFILES = $(CFILES:.c=.o)
COGFILES = $(CFILES:.c=.cogent)
INCLFILES = $(HFILES:.h=-incl.cogent)
COGSRC = $(INCLFILES) $(COGFILES) $(UNITFILES)
INCLPATH = -I.

binary: cards
run: run-cards
cogent: $(COGSRC)
edit: $(EDITFILES)
c: $(UNIT)-gen.c $(UNIT)-gen.h $(UNIT).c
cogent-binary: cogent-cards
cogent-run: run-cogent-cards

.PHONY: clean run-cards run-cogent-cards

STDGUM=$(shell cogent --stdgum-dir)
GENCOTC=$(GENCOT_HOME)/c
GENCOTI=$(GENCOT_HOME)/include
COGPPARGS = --cogent-pp-args="-I$(GENCOTI)"

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

$(UNITFILES): $(UNIT).unit $(UNIT).unit-itemprops $(UNIT)-external.items $(CFILES)
ifeq ($(UNIT), all)
	gencot $(INCLPATH) unit
else
	gencot $(INCLPATH) -u $(UNIT) unit
endif

ed-cards.done: cards.cogent
#	*todo*
	@touch ed-cards.done

$(UNIT)-gen.c $(UNIT)-gen.h $(ACFILESINF): $(COGSRC) $(EDITFILES) $(ACFILES)
	cogent -o $(UNIT)-gen -g $(UNIT).cogent $(COGPPARGS) --infer-c-funcs="$(ACFILES)"

$(UNIT).c $(UNIT)-macros.h $(ACFILESC): $(UNIT)-gen.c $(UNIT)-gen.h $(ACFILESINF) $(UNIT).unit
ifeq ($(UNIT), all)
	auxcog unit
else
	auxcog -u $(UNIT) unit
endif

cogent-cards: $(UNIT).c $(UNIT)-gen.c $(UNIT)-gen.h $(UNIT)-macros.h $(ACFILESC)
	cc -o cogent-cards -I$(STDGUM) -I$(GENCOTC) $(UNIT).c

run-cogent-cards: cogent-cards
	./cogent-cards

clean:
	-rm -f cards
	-rm -f $(COGSRC) $(UNIT)-external.items cards-entry.ac
	-rm -rf comments
	-rm -f $(EDITFILES)
	-rm -f $(UNIT)-gen.c $(UNIT)-gen.h $(ACFILESPP) $(ACFILESINF)
	-rm -f $(UNIT).c $(UNIT)-macros.h $(ACFILESC)
	-rm -f cogent-cards
