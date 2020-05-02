HFILES = cards.h rank.h
CFILES = main.c cards.c rank.c
UNITFILES = all-externs.cogent all-exttypes.cogent all-dvdtypes.cogent all.cogent
EDITFILES = ed-cards.done ed-rank.done ed-main.done
ACFILES = all-externs.ac $(CFILES:.c=-entry.ac)
ACFILESPP = $(ACFILES:.ac=_pp.ac)
ACFILESINF = $(ACFILES:.ac=_pp_inferred.c)
ACFILESC = $(ACFILES:.ac=.c)
OFILES = $(CFILES:.c=.o)
COGFILES = $(CFILES:.c=.cogent)
INCLFILES = $(HFILES:.h=-incl.cogent)
COGSRC = $(INCLFILES) $(COGFILES) $(UNITFILES)

PCFILES = main.c rank.c
PUNITFILES = part-externs.cogent part-exttypes.cogent part-dvdtypes.cogent part.cogent
PEDITFILES = ed-rank.done ed-main.done
PACFILES = part-externs.ac $(PCFILES:.c=-entry.ac)
PACFILESPP = $(PACFILES:.ac=_pp.ac)
PACFILESINF = $(PACFILES:.ac=_pp_inferred.c)
PACFILESC = $(PACFILES:.ac=.c)
PCOGFILES = $(PCFILES:.c=.cogent)
PCOGSRC = $(INCLFILES) $(PCOGFILES) $(PUNITFILES)

binary: cards
run: run-cards
all-cogent: $(COGSRC)
all-edit: $(EDITFILES)
all-c: all-gen.c all-gen.h all.c
all-binary: all-cards
all-run: run-all-cards

part-cogent: $(PCOGSRC)
part-edit: $(PEDITFILES)
part-c: part-gen.c part-gen.h part.c
part-binary: part-cards
part-run: run-part-cards

.PHONY: clean run-cards run-all-cards run-part-cards

STDGUM=$(shell cogent --stdgum-dir)
GENCOTC=$(GENCOT_HOME)/c
GENCOTI=$(GENCOT_HOME)/include
COGPPARGS = --cogent-pp-args="-I$(GENCOTI)"

run-cards: cards
	./cards

cards: $(OFILES)
	$(CC) -o cards $(OFILES)

%-incl.cogent: %.h
	gencot hfile $*.h

# depends on $(INCLFILES) for comment transfer from declarations
%.cogent: %.c %.c-itemprops $(INCLFILES)
	gencot -I. cfile $*.c

$(UNITFILES): all.unit all.unit-itemprops $(CFILES)
	gencot -I. unit all.unit

$(PUNITFILES): part.unit part.unit-itemprops $(PCFILES)
	gencot -I. unit part.unit

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
all-gen.c all-gen.h: $(COGSRC) $(EDITFILES) $(ACFILES)
	cogent -o all-gen -g all.cogent $(COGPPARGS) --infer-c-funcs="$(ACFILES)"

# Implicitly also generates $(PACFILESINF)
part-gen.c part-gen.h: $(PCOGSRC) $(PEDITFILES) $(PACFILES)
	cogent -o part-gen -g part.cogent $(COGPPARGS) --infer-c-funcs="$(PACFILES)"

# Implicitly also generates $(ACFILESC)
all.c all-macros.h: all-gen.c all-gen.h $(ACFILESINF) all.unit
	auxcog unit all.unit

# Implicitly also generates $(PACFILESC)
part.c part-macros.h: part-gen.c part-gen.h $(PACFILESINF) part.unit
	auxcog unit part.unit

all-cards: all.c all-gen.c all-gen.h all-macros.h $(ACFILESC)
	$(CC) -o all-cards -I$(STDGUM) -I$(GENCOTC) all.c

part.o: part.c part-gen.c part-gen.h part-macros.h $(PACFILESC)
	$(CC) -c -I$(STDGUM) -I$(GENCOTC) part.c

part-cards: part.o cards.o
	$(CC) -o part-cards part.o cards.o

run-all-cards: all-cards
	./all-cards

run-part-cards: part-cards
	./part-cards

clean:
	-rm -f cards $(OFILES) part.o
	-rm -f $(COGSRC) $(PCOGSRC)
	-rm -rf comments
	-rm -f $(EDITFILES) $(PEDITFILES)
	-rm -f all-gen.c all-gen.h $(ACFILESPP) $(ACFILESINF) part-gen.c part-gen.h $(PACFILESPP) $(PACFILESINF)
	-rm -f all.c all-macros.h $(ACFILESC) part.c part-macros.h $(PACFILESC)
	-rm -f all-cards part-cards
