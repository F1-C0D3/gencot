HFILES = 
CFILES = hello.c
UNITFILES = unit-externs.cogent unit-exttypes.cogent unit-dvdtypes.cogent unit.cogent
EDITFILES = ed-unit-externs.done ed-hello.done
ACFILES = unit-externs.ac $(CFILES:.c=-entry.ac)
ACFILESPP = $(ACFILES:.ac=_pp.ac)
ACFILESINF = $(ACFILES:.ac=_pp_inferred.c)
ACFILESC = $(ACFILES:.ac=.c)
OFILES = $(CFILES:.c=.o)
COGFILES = $(CFILES:.c=.cogent)
INCLFILES = $(HFILES:.h=-incl.cogent)
COGSRC = $(INCLFILES) $(COGFILES) $(UNITFILES)

binary: hello
run: run-hello
cogent: $(COGSRC)
edit: $(EDITFILES)
cogent-c: unit-gen.c unit-gen.h unit.c
cogent-binary: cogent-hello
cogent-run: run-cogent-hello

.PHONY: clean run-hello run-cogent-hello ed-hello.cogent ed-unit-externs.cogent

STDGUM=$(shell cogent --stdgum-dir)
GENCOTC=$(GENCOT_HOME)/c
GENCOTI=$(GENCOT_HOME)/include
COGPPARGS = --cogent-pp-args="-I$(GENCOTI)"

run-hello: hello
	./hello

%-incl.cogent: %.h
	gencot hfile $*.h

%.cogent: %.c
	gencot cfile $*.c

$(UNITFILES): unit.files $(CFILES)
	gencot unit unit.files

ed-hello.done: hello.cogent
	sed -i -e "4,5d;7d;s/;/; 0/" hello.cogent
	@touch ed-hello.done

ed-unit-externs.done: unit-externs.cogent
	sed -i -e "s/(CPtr U8)\!/String/" unit-externs.cogent
	@touch ed-unit-externs.done

unit-gen.c unit-gen.h $(ACFILESINF): $(COGSRC) $(EDITFILES) $(ACFILES)
	cogent -o unit-gen -g unit.cogent --infer-c-funcs="$(ACFILES)"

unit.c unit-macros.h $(ACFILESC): unit-gen.c unit-gen.h $(ACFILESINF) unit.files
	auxcog unit unit.files

cogent-hello: unit.c unit-gen.c unit-gen.h unit-macros.h $(ACFILESC)
	cc -o cogent-hello -I$(STDGUM) -I$(GENCOTC) unit.c

run-cogent-hello: cogent-hello
	./cogent-hello

clean:
	-rm -f hello
	-rm -f $(COGSRC)
	-rm -f $(EDITFILES)
	-rm -f unit-gen.c unit-gen.h $(ACFILESPP) $(ACFILESINF)
	-rm -f unit.c unit-macros.h $(ACFILESC)
	-rm -f cogent-hello
