UNIT=all

HFILES = cards.h rank.h
ifeq ($(UNIT), all)
CFILES = main.c cards.c rank.c
EDITFILES = ed-cards.done ed-rank.done ed-main.done
COGOFILES = $(UNIT).o
else 
CFILES = main.c rank.c
EDITFILES = ed-rank.done ed-main.done
COGOFILES = $(UNIT).o cards.o
endif

UNITFILES = $(UNIT)-externs.cogent $(UNIT)-exttypes.cogent $(UNIT)-dvdtypes.cogent $(UNIT).cogent
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

cards: $(OFILES)
	$(CC) -o cards $(OFILES)

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

ed-rank.done: rank.cogent
	sed -i -e "6,9d;s/case/if r ==/;10,35s/://;10,35s/return/then/;10,35s/;/ else/;37d;38s/return//;38s/;//;39,41d" rank.cogent
	@touch ed-rank.done

ed-main.done: main.cogent
	sed -i -e "6,7d;14d;s/return 0;/0/" main.cogent
	@touch ed-main.done

# Implicitly also generates $(ACFILESINF)
$(UNIT)-gen.c $(UNIT)-gen.h: $(COGSRC) $(EDITFILES) $(ACFILES)
	cogent -o $(UNIT)-gen -g $(UNIT).cogent $(COGPPARGS) --infer-c-funcs="$(ACFILES)"

# Implicitly also generates $(ACFILESC)
$(UNIT).c $(UNIT)-macros.h: $(UNIT)-gen.c $(UNIT)-gen.h $(ACFILESINF) $(UNIT).unit
ifeq ($(UNIT), all)
	auxcog unit
else
	auxcog -u $(UNIT) unit
endif

$(UNIT).o: $(UNIT).c $(UNIT)-gen.c $(UNIT)-gen.h $(UNIT)-macros.h $(ACFILESC)
	$(CC) -c -I$(STDGUM) -I$(GENCOTC) $(UNIT).c

cogent-cards: $(COGOFILES)
	$(CC) -o cogent-cards $(COGOFILES)

run-cogent-cards: cogent-cards
	./cogent-cards

clean:
	-rm -f cards $(OFILES) $(UNIT).o
	-rm -f $(COGSRC) $(UNIT)-external.items $(CFILES:.c=-entry.ac)
	-rm -rf comments
	-rm -f $(EDITFILES)
	-rm -f $(UNIT)-gen.c $(UNIT)-gen.h $(ACFILESPP) $(ACFILESINF)
	-rm -f $(UNIT).c $(UNIT)-macros.h $(ACFILESC)
	-rm -f cogent-cards
