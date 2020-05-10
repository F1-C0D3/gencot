HFILES = cards.h rank.h
CFILES = cards.c
UNITFILES = all-externs.cogent all-exttypes.cogent all-dvdtypes.cogent all.cogent
EDITFILES = ed-cards.done
ACFILES = all-externs.ac $(CFILES:.c=-entry.ac)
ACFILESPP = $(ACFILES:.ac=_pp.ac)
ACFILESINF = $(ACFILES:.ac=_pp_inferred.c)
ACFILESC = $(ACFILES:.ac=.c)
OFILES = $(CFILES:.c=.o)
COGFILES = $(CFILES:.c=.cogent)
INCLFILES = $(HFILES:.h=-incl.cogent)
COGSRC = $(INCLFILES) $(COGFILES) $(UNITFILES)

binary: cards
run: run-cards
all-cogent: $(COGSRC)
all-edit: $(EDITFILES)
all-c: all-gen.c all-gen.h all.c
all-binary: all-cards
all-run: run-all-cards

.PHONY: clean run-cards run-cogent-cards

STDGUM=$(shell cogent --stdgum-dir)
GENCOTC=$(GENCOT_HOME)/c
GENCOTI=$(GENCOT_HOME)/include
COGPPARGS = --cogent-pp-args="-I$(GENCOTI)"

run-cards: cards
	./cards

%-incl.cogent: %.h
	gencot hfile $*.h

# depends on $(INCLFILES) for comment transfer from declarations
%.cogent: %.c %.c-itemprops $(INCLFILES)
	gencot -I. cfile $*.c

$(UNITFILES): all.unit all.unit-itemprops $(CFILES)
	gencot -I. unit

ed-cards.done: cards.cogent
#	*todo*
	@touch ed-cards.done

all-gen.c all-gen.h $(ACFILESINF): $(COGSRC) $(EDITFILES) $(ACFILES)
	cogent -o all-gen -g all.cogent $(COGPPARGS) --infer-c-funcs="$(ACFILES)"

all.c all-macros.h $(ACFILESC): all-gen.c all-gen.h $(ACFILESINF) all.unit
	auxcog unit

all-cards: all.c all-gen.c all-gen.h all-macros.h $(ACFILESC)
	cc -o all-cards -I$(STDGUM) -I$(GENCOTC) all.c

run-all-cards: all-cards
	./all-cards

clean:
	-rm -f cards
	-rm -f $(COGSRC)
	-rm -rf comments
	-rm -f $(EDITFILES)
	-rm -f all-gen.c all-gen.h $(ACFILESPP) $(ACFILESINF)
	-rm -f all.c all-macros.h $(ACFILESC)
	-rm -f all-cards
