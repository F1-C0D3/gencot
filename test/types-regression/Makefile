GC=../../bin/gencot
IT=../../bin/items

TESTS = prim enum struct union array func parmod pointer names const extrefs
UNIT = externs exttypes dvdtypes
ABSINCL = -I/home/teege/work/projekte/code/HoBit/devel/gencot/test/types-regression
AUNIT = unit-dfltprops
PPROPS = types-parmod.json-itemprops types-parmod.json-omitprops

compile: $(foreach TST,$(TESTS),types-$(TST).o)

cogent: $(foreach TST,$(TESTS),types-$(TST).cogent) unit

dfltprops: $(foreach TST,$(TESTS),types-$(TST).c-dfltprops) test.unit-dfltprops

itemprops: $(foreach TST,$(TESTS),types-$(TST).c-itemprops)

regression: $(foreach TST,$(TESTS),$(TST)-regression) unit-regression

expect-current: $(foreach TST,$(TESTS),$(TST)-expect-current) unit-expect-current

clean:  $(foreach TST,$(TESTS),$(TST)-clean)
	-rm -f test.unit test.cogent $(foreach U,$(UNIT),test-$(U).cogent)
	-rm -f test-external.items test.unit-dfltprops test.unit-itemprops

types-pointer.c-itemprops: types-pointer.c-manprops types-pointer.c-dfltprops types-parmod.json-itemprops
	@$(IT) mergeto types-pointer.c-dfltprops types-parmod.json-itemprops > types-pointer.c-hprops
	@$(IT) merge common.types-manprops types-pointer.c-hprops > types-pointer.c-h2props
	@$(IT) merge types-pointer.c-h2props types-pointer.c-manprops > types-pointer.c-itemprops
	@rm types-pointer.c-hprops types-pointer.c-h2props

types-const.c-itemprops: types-const.c-manprops types-const.c-dfltprops types-parmod.json-itemprops
	@$(IT) mergeto types-const.c-dfltprops types-parmod.json-itemprops > types-const.c-hprops
	@$(IT) merge common.types-manprops types-const.c-hprops > types-const.c-h2props
	@$(IT) merge types-const.c-h2props types-const.c-manprops > types-const.c-itemprops
	@rm types-const.c-hprops types-const.c-h2props

types-extrefs.c-itemprops: types-extrefs.c-dfltprops $(PPROPS) common.types-manprops test.unit-dfltprops test.unit-manprops
	@$(IT) merge types-extrefs.c-dfltprops test.unit-dfltprops > types-extrefs.c-hprops
	@$(IT) mergeto types-extrefs.c-hprops types-parmod.json-itemprops > types-extrefs.c-h2props
	@$(IT) omitfrom types-extrefs.c-h2props types-parmod.json-omitprops > types-extrefs.c-hprops
	@$(IT) merge types-extrefs.c-hprops common.types-manprops > types-extrefs.c-h2props
	@$(IT) merge types-extrefs.c-h2props test.unit-manprops > types-extrefs.c-itemprops
	@rm types-extrefs.c-hprops types-extrefs.c-h2props

%.c-itemprops: %.c-dfltprops $(PPROPS) common.types-manprops
	@$(IT) mergeto $*.c-dfltprops types-parmod.json-itemprops > $*.c-hprops
	@$(IT) omitfrom $*.c-hprops types-parmod.json-omitprops > $*.c-h2props
	@$(IT) merge common.types-manprops $*.c-h2props > $*.c-itemprops
	@rm $*.c-hprops $*.c-h2props

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

unit-expect-current: unit
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
	@$(IT) $(ABSINCL) -u test unit > test.unit-dfltprops

test-external.items: test.unit test.unit-manitems 
	@$(IT) $(ABSINCL) -u test used

%.c-dfltprops: %.c
	@$(IT) $(ABSINCL) file $*.c > $*.c-dfltprops

%.cogent: %.c %.c-itemprops test-external.items
	@$(GC) $(ABSINCL) -u test cfile $*.c

%-regression: types-%.cogent types-%-expected.cogent types-%.c-dfltprops types-%-expected.c-dfltprops
	-diff types-$*.cogent types-$*-expected.cogent
	-diff types-$*.c-dfltprops types-$*-expected.c-dfltprops

%-expect-current: types-%.cogent types-%.c-dfltprops
	cp types-$*.cogent types-$*-expected.cogent
	cp types-$*.c-dfltprops types-$*-expected.c-dfltprops

%-clean:
	-rm -f types-$*.cogent types-$*.o types-$*.c-dfltprops types-$*.c-itemprops

test.unit-itemprops: itemprops
	@touch test.unit-itemprops
	@for f in $(foreach TST,$(TESTS),types-$(TST).c-itemprops); do \
	  $(IT) merge $$f test.unit-itemprops > iprops; \
	  mv iprops test.unit-itemprops; \
	done

test.unit: 
	@for f in $(foreach TST,$(TESTS),types-$(TST).c); do \
	  echo $$f >> test.unit; \
	done
	@cat test.unit

unit: test.unit test.unit-itemprops
	@$(GC) $(ABSINCL) -u test unit
