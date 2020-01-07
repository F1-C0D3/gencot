binary: hello
run: run-hello
cogent: hello.cogent
edit: ed-hello.cogent ed-hello-externs.cogent ed-hello-externs.ac
cogent-c: unit.c unit.h
cogent-binary: cogent-hello
cogent-run: run-cogent-hello

STDGUM=$(shell cogent --stdgum-dir)

run-hello: hello
	./hello

hello.cogent: hello.c
	gencot cfile hello.c
	gencot unit hello.unit

ed-hello.cogent: hello.cogent
	sed -e "4,5d;7d;s/;/; 0/" hello.cogent > ed-hello.cogent

ed-hello-externs.cogent: hello-externs.cogent
	sed -e "s/(CPtr U8)\!/String/" hello-externs.cogent > ed-hello-externs.cogent

unit.c: unit.cogent ed-hello.cogent ed-hello-externs.cogent ed-hello-externs.ac hello-entry.ac
	cogent -g unit.cogent --infer-c-funcs="ed-hello-externs.ac hello-entry.ac"

cogent-hello: cogent-hello.c unit.c unit.h ed-hello-externs_pp_inferred.c hello-entry_pp_inferred.c
	cc -o cogent-hello -I$(STDGUM) cogent-hello.c

run-cogent-hello: cogent-hello
	./cogent-hello

clean:
	-rm hello
	-rm hello.cogent hello-*.cogent
	-rm ed-hello.cogent ed-hello-*.cogent
	-rm unit.c unit.h ed-hello-*_pp.ac ed-hello-*_pp_inferred.c hello-entry_pp.ac hello-entry_pp_inferred.c
	-rm cogent-hello
