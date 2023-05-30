GC=../../bin/gencot
IT=../../bin/items

#VARIANT = plaingen
#TCONF = -tflbG

#VARIANT = plain
#TCONF = -tflb

VARIANT = banggen
TCONF = -tflG

#VARIANT = bangproc
#TCONF = -tfl

#VARIANT = letproc
#TCONF = -tfb
#TCONF = -tf

#VARIANT = ifproc
#TCONF = -tb
#TCONF =

TESTS = purexpr assignexpr stat loop func ro
UNIT = externs exttypes dvdtypes
AUNIT = unit-dfltprops

compile: $(foreach TST,$(TESTS),body-$(TST).o)

cogent: $(foreach TST,$(TESTS),body-$(TST).cogent) unit

dfltprops: $(foreach TST,$(TESTS),body-$(TST).c-dfltprops) test.unit-dfltprops

mixprops: $(foreach TST,$(TESTS),body-$(TST).c-mixprops) test.unit-mixprops

regression: $(foreach TST,$(TESTS),$(TST)-regression) unit-regression

expect-current: $(foreach TST,$(TESTS),$(TST)-expect-current) unit-expect-current

clean:  $(foreach TST,$(TESTS),$(TST)-clean)
	-rm -f test.unit test.unit-errmess test.cogent $(foreach U,$(UNIT),test-$(U).cogent)
	-rm -f test-external.items test.unit-dfltprops test.unit-mixprops test.unit-itemprops

%.c-mixprops: %.c-dfltprops
	@cp $*.c-dfltprops $@
	@if [ -e $*.c-manprops ]; \
	then \
		$(IT) mergeto $@ $*.c-manprops > $*-hprops; mv $*-hprops $@; \
	fi

%.c-itemprops: %.c-mixprops test.unit-mixprops common.types-manprops
	@$(IT) merge $*.c-mixprops test.unit-mixprops > $@
	@$(IT) merge common.types-manprops $@ > $*-hprops; mv $*-hprops $@

unit-regression: unit $(foreach U,$(UNIT),$(VARIANT)/test-$(U)-expected.cogent) $(foreach U,$(AUNIT),test.$(U) $(VARIANT)/test-expected.$(U)) test-external.items $(VARIANT)/test-external-expected.items
	-@for u in $(UNIT); do \
	  echo "diff test-$$u.cogent $(VARIANT)/test-$$u-expected.cogent"; \
	  diff test-$$u.cogent $(VARIANT)/test-$$u-expected.cogent; \
	done
	-@for u in $(AUNIT); do \
	  echo "diff test.$$u $(VARIANT)/test-expected.$$u"; \
	  diff test.$$u $(VARIANT)/test-expected.$$u; \
	done
	-diff test-external.items $(VARIANT)/test-external-expected.items
	-diff test.unit-errmess $(VARIANT)/test.unit-expected-errmess

unit-expect-current: unit test.unit-dfltprops
	@for u in $(UNIT); do \
	  echo "cp test-$$u.cogent $(VARIANT)/test-$$u-expected.cogent"; \
	  cp test-$$u.cogent $(VARIANT)/test-$$u-expected.cogent; \
	done
	@for u in $(AUNIT); do \
	  echo "cp test.$$u $(VARIANT)/test-expected.$$u"; \
	  cp test.$$u $(VARIANT)/test-expected.$$u; \
	done
	cp test-external.items $(VARIANT)/test-external-expected.items
	cp test.unit-errmess $(VARIANT)/test.unit-expected-errmess

test.unit-dfltprops: test.unit test-external.items
	@$(IT) -u test unit > test.unit-dfltprops

test-external.items: test.unit test.unit-manitems 
	@$(IT) -u test used

%.c-dfltprops: %.c
	@$(IT) file $*.c > $*.c-dfltprops

%.cogent %-entry.ac %-errmess: %.c %.c-itemprops test-external.items
	@$(GC) -u test $(TCONF) cfile $*.c 2> $*-errmess

%-regression: body-%.cogent $(VARIANT)/body-%-expected.cogent body-%.c-dfltprops $(VARIANT)/body-%-expected.c-dfltprops
	-diff body-$*.cogent $(VARIANT)/body-$*-expected.cogent
	-diff body-$*.c-dfltprops $(VARIANT)/body-$*-expected.c-dfltprops
	-diff body-$*-entry.ac $(VARIANT)/body-$*-entry-expected.ac
	-diff body-$*-errmess $(VARIANT)/body-$*-expected-errmess

%-expect-current: body-%.cogent body-%.c-dfltprops
	cp body-$*.cogent $(VARIANT)/body-$*-expected.cogent
	cp body-$*.c-dfltprops $(VARIANT)/body-$*-expected.c-dfltprops
	cp body-$*-entry.ac $(VARIANT)/body-$*-entry-expected.ac
	cp body-$*-errmess $(VARIANT)/body-$*-expected-errmess

%-clean:
	-rm -f body-$*.cogent body-$*.o body-$*.c-dfltprops body-$*.c-itemprops body-$*.c-mixprops body-$*-entry.ac body-$*-errmess

test.unit-mixprops: test.unit-dfltprops test.unit-manprops
	@$(IT) mergeto test.unit-dfltprops test.unit-manprops > $@

test.unit-itemprops: mixprops common.types-manprops
	@cp test.unit-mixprops $@
	@for f in $(foreach TST,$(TESTS),body-$(TST).c-mixprops); do \
	  $(IT) merge $$f $@ > hprops; mv hprops $@; \
	done
	@$(IT) merge common.types-manprops $@ > hprops; mv hprops $@

test.unit: 
	@for f in $(foreach TST,$(TESTS),body-$(TST).c); do \
	  echo $$f >> test.unit; \
	done
	@cat test.unit

unit: test.unit test.unit-itemprops
	@$(GC) -u test unit 2> test.unit-errmess
