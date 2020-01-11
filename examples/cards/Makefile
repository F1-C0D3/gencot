UNITFILES = unit-externs.cogent unit-exttypes.cogent unit-dvdtypes.cogent
EDUNITFILES = ed-unit-externs.cogent unit-exttypes.cogent unit-dvdtypes.cogent unit-externs.ac
ACFILES = unit-externs.ac cards-entry.ac
ACFILESPP = $(ACFILES:.ac=_pp.ac)
ACFILESINF = $(ACFILES:.ac=_pp_inferred.c)
HFILES = cards.h rank.h
INCLFILES = $(HFILES:.h=-incl.cogent)

binary: cards
run: run-cards
cogent: $(INCLFILES) cards.cogent $(UNITFILES)
edit: ed-cards.cogent $(EDUNITFILES)
cogent-c: gen-unit.c gen-unit.h
cogent-binary: cogent-cards
cogent-run: run-cogent-cards

.PHONY: clean run-cards run-cogent-cards

STDGUM=$(shell cogent --stdgum-dir)

run-cards: cards
	./cards

%-incl.cogent: %.h
	gencot hfile $*.h

cards.cogent: cards.c
	gencot -I. cfile cards.c

$(UNITFILES): unit.files cards.c
	gencot -I. unit unit.files

ed-cards.cogent: cards.cogent
	sed -e "4,5d;7d;s/;/; 0/" cards.cogent > ed-cards.cogent

ed-unit-externs.cogent: unit-externs.cogent
	sed -e "s/(CPtr U8)\!/String/" unit-externs.cogent > ed-unit-externs.cogent

gen-unit.c gen-unit.h: unit.cogent ed-cards.cogent cards-entry.ac $(EDUNITFILES)
	cogent -o gen-unit -g unit.cogent --infer-c-funcs="$(ACFILES)"

cogent-cards: unit.c gen-unit.c gen-unit.h $(ACFILESINF)
	cc -o cogent-cards -I$(STDGUM) unit.c

run-cogent-cards: cogent-cards
	./cogent-cards

clean:
	-rm cards
	-rm cards.cogent $(INCLFILES) $(UNITFILES)
	-rm -r comments
	-rm ed-cards.cogent ed-unit-*.cogent
	-rm gen-unit.c gen-unit.h $(ACFILESPP) $(ACFILESINF)
	-rm cogent-cards
