UNITFILES = unit-externs.cogent unit-exttypes.cogent unit-dvdtypes.cogent unit.cogent
EDUNITFILES = ed-unit-externs.cogent unit-exttypes.cogent unit-dvdtypes.cogent unit-externs.ac
ACFILES = unit-externs.ac hello-entry.ac
ACFILESPP = $(ACFILES:.ac=_pp.ac)
ACFILESINF = $(ACFILES:.ac=_pp_inferred.c)

binary: hello
run: run-hello
cogent: hello.cogent $(UNITFILES)
edit: ed-hello.cogent $(EDUNITFILES)
cogent-c: unit-gen.c unit-gen.h unit.c
cogent-binary: cogent-hello
cogent-run: run-cogent-hello

.PHONY: clean run-hello run-cogent-hello ed-hello.cogent ed-unit-externs.cogent

STDGUM=$(shell cogent --stdgum-dir)

run-hello: hello
	./hello

hello.cogent: hello.c
	gencot cfile hello.c

$(UNITFILES): unit.files hello.c
	gencot unit unit.files

ed-hello.cogent: hello.cogent
	@if grep '{-' hello.cogent; \
	then sed -i -e "4,5d;7d;s/;/; 0/" hello.cogent; \
	fi

ed-unit-externs.cogent: unit-externs.cogent
	@if grep 'CPtr' unit-externs.cogent; \
	then sed -i -e "s/(CPtr U8)\!/String/" unit-externs.cogent; \
	fi

unit-gen.c unit-gen.h: unit.cogent ed-hello.cogent hello-entry.ac $(EDUNITFILES)
	cogent -o unit-gen -g unit.cogent --infer-c-funcs="$(ACFILES)"

unit.c: unit.files 
	auxcog unit unit.files

cogent-hello: unit.c unit-gen.c unit-gen.h $(ACFILESINF)
	cc -o cogent-hello -I$(STDGUM) unit.c

run-cogent-hello: cogent-hello
	./cogent-hello

clean:
	-rm -f hello
	-rm -f hello.cogent $(UNITFILES)
	-rm -f unit-gen.c unit-gen.h $(ACFILESPP) $(ACFILESINF)
	-rm -f cogent-hello
