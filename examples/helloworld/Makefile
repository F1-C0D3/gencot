HFILES = 
CFILES = hello.c
UNITFILES = all-externs.cogent all-exttypes.cogent all-dvdtypes.cogent all.cogent
EDITFILES = ed-all-externs.done ed-hello.done
ACFILES = all-externs.ac $(CFILES:.c=-entry.ac)
ACFILESPP = $(ACFILES:.ac=_pp.ac)
ACFILESINF = $(ACFILES:.ac=_pp_inferred.c)
ACFILESC = $(ACFILES:.ac=.c)
OFILES = $(CFILES:.c=.o)
COGFILES = $(CFILES:.c=.cogent)
INCLFILES = $(HFILES:.h=-incl.cogent)
COGSRC = $(INCLFILES) $(COGFILES) $(UNITFILES)

binary: hello
run: run-hello
all-cogent: $(COGSRC)
all-edit: $(EDITFILES)
all-c: all-gen.c all-gen.h all.c
all-binary: all-hello
all-run: run-all-hello

.PHONY: clean run-hello run-cogent-hello ed-hello.cogent ed-all-externs.cogent

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

$(UNITFILES): all.unit $(CFILES)
	gencot unit all.unit

ed-hello.done: hello.cogent
	sed -i -e "4,5d;7d;s/;/; 0/" hello.cogent
	@touch ed-hello.done

ed-all-externs.done: all-externs.cogent
	sed -i -e "s/(MayNull (CPtr U8))\!/String/" all-externs.cogent
	@touch ed-all-externs.done

all-gen.c all-gen.h $(ACFILESINF): $(COGSRC) $(EDITFILES) $(ACFILES)
	cogent -o all-gen -g all.cogent --infer-c-funcs="$(ACFILES)"

all.c all-macros.h $(ACFILESC): all-gen.c all-gen.h $(ACFILESINF) all.unit
	auxcog unit all.unit

all-hello: all.c all-gen.c all-gen.h all-macros.h $(ACFILESC)
	cc -o all-hello -I$(STDGUM) -I$(GENCOTC) all.c

run-all-hello: all-hello
	./all-hello

clean:
	-rm -f hello
	-rm -f $(COGSRC)
	-rm -f $(EDITFILES)
	-rm -f all-gen.c all-gen.h $(ACFILESPP) $(ACFILESINF)
	-rm -f all.c all-macros.h $(ACFILESC)
	-rm -f all-hello
