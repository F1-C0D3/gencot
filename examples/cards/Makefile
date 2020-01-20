HFILES = cards.h rank.h
CFILES = cards.c
UNITFILES = unit-externs.cogent unit-exttypes.cogent unit-dvdtypes.cogent unit.cogent
EDITFILES = ed-unit-externs.done ed-cards.done
ACFILES = unit-externs.ac $(CFILES:.c=-entry.ac)
ACFILESPP = $(ACFILES:.ac=_pp.ac)
ACFILESINF = $(ACFILES:.ac=_pp_inferred.c)
ACFILESC = $(ACFILES:.ac=.c)
OFILES = $(CFILES:.c=.o)
COGFILES = $(CFILES:.c=.cogent)
INCLFILES = $(HFILES:.h=-incl.cogent)
COGSRC = $(INCLFILES) $(COGFILES) $(UNITFILES)

binary: cards
run: run-cards
cogent: $(COGSRC)
edit: $(EDITFILES)
cogent-c: unit-gen.c unit-gen.h unit.c
cogent-binary: cogent-cards
cogent-run: run-cogent-cards

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
%.cogent: %.c $(INCLFILES)
	gencot -I. cfile $*.c

$(UNITFILES): unit.files $(CFILES)
	gencot -I. unit unit.files

ed-cards.done: cards.cogent
#	*todo*
	sed -i -e "s/CPtr U8/String/" cards.cogent
	@touch ed-cards.done

ed-unit-externs.done: unit-externs.cogent
	sed -i -e "s/(CPtr U8)\!/String/" unit-externs.cogent
	@touch ed-unit-externs.done

unit-gen.c unit-gen.h $(ACFILESINF): $(COGSRC) $(EDITFILES) $(ACFILES)
	cogent -o unit-gen -g unit.cogent $(COGPPARGS) --infer-c-funcs="$(ACFILES)"

unit.c unit-macros.h $(ACFILESC): unit-gen.c unit-gen.h $(ACFILESINF) unit.files
	auxcog unit unit.files

cogent-cards: unit.c unit-gen.c unit-gen.h unit-macros.h $(ACFILESC)
	cc -o cogent-cards -I$(STDGUM) -I$(GENCOTC) unit.c

run-cogent-cards: cogent-cards
	./cogent-cards

clean:
	-rm -f cards
	-rm -f $(COGSRC)
	-rm -rf comments
	-rm -f $(EDITFILES)
	-rm -f unit-gen.c unit-gen.h $(ACFILESPP) $(ACFILESINF)
	-rm -f unit.c unit-macros.h $(ACFILESC)
	-rm -f cogent-cards