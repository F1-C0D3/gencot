GC=../../bin/gencot
IT=../../bin/items

TESTS = purexpr assignexpr stat loop
UNIT = externs exttypes dvdtypes
AUNIT = unit-dfltprops

compile: $(foreach TST,$(TESTS),body-$(TST).o)

cogent: $(foreach TST,$(TESTS),body-$(TST).cogent) unit

dfltprops: $(foreach TST,$(TESTS),body-$(TST).c-dfltprops) test.unit-dfltprops

itemprops: $(foreach TST,$(TESTS),body-$(TST).c-itemprops)

regression: $(foreach TST,$(TESTS),$(TST)-regression) unit-regression

expect-current: $(foreach TST,$(TESTS),$(TST)-expect-current) unit-expect-current

clean:  $(foreach TST,$(TESTS),$(TST)-clean)
	-rm -f test.unit test.cogent $(foreach U,$(UNIT),test-$(U).cogent)
	-rm -f test-external.items test.unit-dfltprops test.unit-itemprops

%.c-itemprops: %.c-dfltprops common.types-manprops
	@$(IT) merge common.types-manprops $*.c-dfltprops > $*.c-itemprops

unit-regression: unit $(foreach U,$(UNIT),test-$(U)-expected.cogent) $(foreach U,$(AUNIT),test.$(U) test-expected.$(U)) test-external.items test-external-expected.items
	-@for u in $(UNIT); do \
	  echo "diff test-$$u.cogent test-$$u-expected.cogent"; \
	  diff test-$$u.cogent test-$$u-expected.cogent; \
	done
	-@for u in $(AUNIT); do \
	  echo "diff test.$$u test-expected.$$u"; \
	  diff test.$$u test-expected.$$u; \
	done
	-diff test-external.items test-external-expected.items

unit-expect-current: unit test.unit-dfltprops
	@for u in $(UNIT); do \
	  echo "cp test-$$u.cogent test-$$u-expected.cogent"; \
	  cp test-$$u.cogent test-$$u-expected.cogent; \
	done
	@for u in $(AUNIT); do \
	  echo "cp test.$$u test-expected.$$u"; \
	  cp test.$$u test-expected.$$u; \
	done
	cp test-external.items test-external-expected.items

test.unit-dfltprops: test.unit test-external.items
	@$(IT) -u test unit > test.unit-dfltprops

test-external.items: test.unit test.unit-manitems 
	@$(IT) -u test used

%.c-dfltprops: %.c
	@$(IT) file $*.c > $*.c-dfltprops

%.cogent %-entry.ac: %.c %.c-itemprops test-external.items
	@$(GC) -u test cfile $*.c

%-regression: body-%.cogent body-%-expected.cogent body-%.c-dfltprops body-%-expected.c-dfltprops
	-diff body-$*.cogent body-$*-expected.cogent
	-diff body-$*.c-dfltprops body-$*-expected.c-dfltprops
	-diff body-$*-entry.ac body-$*-entry-expected.ac

%-expect-current: body-%.cogent body-%.c-dfltprops
	cp body-$*.cogent body-$*-expected.cogent
	cp body-$*.c-dfltprops body-$*-expected.c-dfltprops
	cp body-$*-entry.ac body-$*-entry-expected.ac

%-clean:
	-rm -f body-$*.cogent body-$*.o body-$*.c-dfltprops body-$*.c-itemprops body-$*-entry.ac

test.unit-itemprops: itemprops
	@touch test.unit-itemprops
	@for f in $(foreach TST,$(TESTS),body-$(TST).c-itemprops); do \
	  $(IT) merge $$f test.unit-itemprops > iprops; \
	  mv iprops test.unit-itemprops; \
	done

test.unit: 
	@for f in $(foreach TST,$(TESTS),body-$(TST).c); do \
	  echo $$f >> test.unit; \
	done
	@cat test.unit

unit: test.unit test.unit-itemprops
	@$(GC) -u test unit