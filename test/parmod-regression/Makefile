PM=../../bin/parmod

TESTS = test

compile: $(foreach TST,$(TESTS),parmod-$(TST).o)

json: $(foreach TST,$(TESTS),parmod-$(TST).json)

close-json: $(foreach TST,$(TESTS),parmod-$(TST)-close.json)

regression: $(foreach TST,$(TESTS),$(TST)-regression)

expect-current: $(foreach TST,$(TESTS),$(TST)-expect-current)

clean:  $(foreach TST,$(TESTS),$(TST)-clean)

%-close.json: %.c
	@$(PM) close $*.c > $*-close.json

%.json: %.c
	@$(PM) init $*.c > $*.json

%.json-itemprops %.json-omitprops: %.json
	@$(PM) out $*.json

%-regression: parmod-%.json parmod-%-expected.json parmod-%-close.json parmod-%-close-expected.json
	-diff parmod-$*.json parmod-$*-expected.json
	-diff parmod-$*-close.json parmod-$*-close-expected.json

%-expect-current:  parmod-%.json parmod-%-close.json
	cp parmod-$*.json parmod-$*-expected.json
	cp parmod-$*-close.json parmod-$*-close-expected.json

%-clean:
	-rm -f parmod-$*.json parmod-$*-close.json parmod-$*.o
	-rm -f parmod-$*.json-itemprops parmod-$*.json-omitprops

