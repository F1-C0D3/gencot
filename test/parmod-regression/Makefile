PM=../../bin/parmod
IT=../../bin/items

TESTS = test
ABSINCL = -I/home/teege/work/projekte/code/HoBit/devel/gencot/test/parmod-regression

compile: $(foreach TST,$(TESTS),parmod-$(TST).o)

json: $(foreach TST,$(TESTS),parmod-$(TST).json)

close-json: $(foreach TST,$(TESTS),parmod-$(TST)-close.json)

regression: $(foreach TST,$(TESTS),$(TST)-regression)

expect-current: $(foreach TST,$(TESTS),$(TST)-expect-current)

clean:  $(foreach TST,$(TESTS),$(TST)-clean)

parmod.unit:
	@for f in $(foreach TST,$(TESTS),parmod-$(TST).c); do \
	  echo $$f >> parmod.unit; \
	done

parmod.extitems: parmod.unit
	@$(IT) $(ABSINCL) used parmod.unit > parmod.extitems

%-close.json: %.c parmod.extitems
	@$(PM) $(ABSINCL) close $*.c parmod.extitems > $*-close.json

%.json: %.c parmod.extitems
	@$(PM) $(ABSINCL) init $*.c parmod.extitems > $*.json

%.json-itemprops %.json-omitprops: %.json
	@$(PM) out $*.json

%-regression: parmod-%.json parmod-%-expected.json parmod-%-close.json parmod-%-close-expected.json
	-diff parmod-$*.json parmod-$*-expected.json
	-diff parmod-$*-close.json parmod-$*-close-expected.json

%-expect-current:  parmod-%.json parmod-%-close.json
	cp parmod-$*.json parmod-$*-expected.json
	cp parmod-$*-close.json parmod-$*-close-expected.json

%-clean:
	-rm -f parmod-$*.json parmod-$*-close.json parmod-$*.o parmod.unit parmod.extitems
	-rm -f parmod-$*.json-itemprops parmod-$*.json-omitprops

