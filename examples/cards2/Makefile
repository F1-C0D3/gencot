HFILES = cards.h rank.h
CFILES = main.c cards.c rank.c
UNITFILES = unit-externs.cogent unit-exttypes.cogent unit-dvdtypes.cogent unit.cogent
EDITFILES = ed-unit-externs.done ed-cards.done ed-rank.done
ACFILES = unit-externs.ac $(CFILES:.c=-entry.ac)
ACFILESPP = $(ACFILES:.ac=_pp.ac)
ACFILESINF = $(ACFILES:.ac=_pp_inferred.c)
ACFILESC = $(ACFILES:.ac=.c)
OFILES = $(CFILES:.c=.o)
COGFILES = $(CFILES:.c=.cogent)
INCLFILES = $(HFILES:.h=-incl.cogent)
COGSRC = $(INCLFILES) $(COGFILES) $(UNITFILES)

PCFILES = main.c rank.c
PUNITFILES = part-externs.cogent part-exttypes.cogent part-dvdtypes.cogent part.cogent
PEDITFILES = ed-part-externs.done ed-rank.done
PACFILES = part-externs.ac $(PCFILES:.c=-entry.ac)
PACFILESPP = $(PACFILES:.ac=_pp.ac)
PACFILESINF = $(PACFILES:.ac=_pp_inferred.c)
PACFILESC = $(PACFILES:.ac=.c)
PCOGFILES = $(PCFILES:.c=.cogent)
PCOGSRC = $(INCLFILES) $(PCOGFILES) $(PUNITFILES)

binary: cards
run: run-cards
cogent: $(COGSRC)
edit: $(EDITFILES)
cogent-c: unit-gen.c unit-gen.h unit.c
cogent-binary: cogent-cards
cogent-run: run-cogent-cards

part-cogent: $(PCOGSRC)
part-edit: $(PEDITFILES)
part-cogent-c: part-gen.c part-gen.h part.c
part-cogent-binary: part-cogent-cards
part-cogent-run: run-part-cogent-cards

.PHONY: clean run-cards run-cogent-cards run-part-cogent-cards

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

%.cogent: %.c
	gencot -I. cfile $*.c

$(UNITFILES): unit.files $(CFILES)
	gencot -I. unit unit.files

$(PUNITFILES): part.files $(PCFILES)
	gencot -I. unit part.files

ed-cards.done: cards.cogent
#	*todo*
	@touch ed-cards.done

ed-rank.done: rank.cogent
	sed -i -e "s/CPtr U8/String/" rank.cogent
	@touch ed-rank.done

ed-unit-externs.done: unit-externs.cogent
	sed -i -e "s/(CPtr U8)\!/String/" unit-externs.cogent
	@touch ed-unit-externs.done

ed-part-externs.done: part-externs.cogent
	sed -i -e "s/(CPtr U8)\!/String/" part-externs.cogent
	@touch ed-part-externs.done

# Implicitly also generates $(ACFILESINF)
unit-gen.c unit-gen.h: $(COGSRC) $(EDITFILES) $(ACFILES)
	cogent -o unit-gen -g unit.cogent $(COGPPARGS) --infer-c-funcs="$(ACFILES)"

# Implicitly also generates $(PACFILESINF)
part-gen.c part-gen.h: $(PCOGSRC) $(PEDITFILES) $(PACFILES)
	cogent -o part-gen -g part.cogent $(COGPPARGS) --infer-c-funcs="$(PACFILES)"

# Implicitly also generates $(ACFILESC)
unit.c unit-macros.h: unit-gen.c unit-gen.h $(ACFILESINF) unit.files
	auxcog unit unit.files

# Implicitly also generates $(PACFILESC)
part.c part-macros.h: part-gen.c part-gen.h $(PACFILESINF) part.files
	auxcog unit part.files

cogent-cards: unit.c unit-gen.c unit-gen.h unit-macros.h $(ACFILESC)
	$(CC) -o cogent-cards -I$(STDGUM) -I$(GENCOTC) unit.c

part.o: part.c part-gen.c part-gen.h part-macros.h $(PACFILESC)
	$(CC) -c -I$(STDGUM) -I$(GENCOTC) part.c

part-cogent-cards: part.o cards.o
	$(CC) -o part-cogent-cards part.o cards.o

run-cogent-cards: cogent-cards
	./cogent-cards

run-part-cogent-cards: part-cogent-cards
	./part-cogent-cards

clean:
	-rm -f cards $(OFILES) part.o
	-rm -f $(COGSRC) $(PCOGSRC)
	-rm -rf comments
	-rm -f $(EDITFILES) $(PEDITFILES)
	-rm -f unit-gen.c unit-gen.h $(ACFILESPP) $(ACFILESINF) part-gen.c part-gen.h $(PACFILESPP) $(PACFILESINF)
	-rm -f unit.c unit-macros.h $(ACFILESC) part.c part-macros.h $(PACFILESC)
	-rm -f cogent-cards part-cogent-cards
