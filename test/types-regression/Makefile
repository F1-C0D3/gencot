GC=../../bin/gencot

TESTS = prim enum struct union array func parmod pointer names const
UNIT = externs exttypes dvdtypes

compile: $(foreach TST,$(TESTS),types-$(TST).o)

cogent: $(foreach TST,$(TESTS),types-$(TST).cogent) unit

regression: $(foreach TST,$(TESTS),$(TST)-regression) unit-regression

expect-current: $(foreach TST,$(TESTS),$(TST)-expect-current) unit-expect-current

clean:  $(foreach TST,$(TESTS),$(TST)-clean)
	-rm -f unit.files $(foreach U,$(UNIT),unit-$(U).cogent)

types-parmod.cogent: types-parmod.c
	$(GC) cfile types-parmod.c types-parmod.json

unit-regression: unit $(foreach U,$(UNI),unit-$(U)-expected.cogent)
	-@for u in $(UNIT); do \
	  echo "diff unit-$$u.cogent unit-$$u-expected.cogent"; \
	  diff unit-$$u.cogent unit-$$u-expected.cogent; \
	done

unit-expect-current: unit
	@for u in $(UNIT); do \
	  echo "cp unit-$$u.cogent unit-$$u-expected.cogent"; \
	  cp unit-$$u.cogent unit-$$u-expected.cogent; \
	done

%.cogent: %.c
	$(GC) cfile $*.c

%-regression: types-%.cogent types-%-expected.cogent
	-diff types-$*.cogent types-$*-expected.cogent

%-expect-current: types-%.cogent
	cp types-$*.cogent types-$*-expected.cogent

%-clean:
	-rm -f types-$*.cogent types-$*.o

unit.files: 
	@for f in $(foreach TST,$(TESTS),types-$(TST).c); do \
	  echo $$f >> unit.files; \
	done
	@cat unit.files

unit: unit.files
	$(GC) unit unit.files types-parmod.json
