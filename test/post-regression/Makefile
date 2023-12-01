CP=../../bin/cogent-proc
GD=../../bin/gencot-defcomments

#OPTION = -i
#VARIANT = noproc

#OPTION = -l
#VARIANT = letproc

OPTION = -f
VARIANT = ifproc

TESTS = nolet letsingle letmulti ifexpr

out: $(foreach TST,$(TESTS),post-$(TST)-out.cogent)

regression: $(foreach TST,$(TESTS),$(TST)-regression)

expect-current: $(foreach TST,$(TESTS),$(TST)-expect-current)

clean:  $(foreach TST,$(TESTS),$(TST)-clean)

%-out.cogent: %.cogent
	@$(CP) $(OPTION) $*.cogent | $(GD) dummy > $*-out.cogent

%-regression: post-%-out.cogent $(VARIANT)/post-%-expected.cogent
	-diff post-$*-out.cogent $(VARIANT)/post-$*-expected.cogent

%-expect-current: post-%-out.cogent
	cp post-$*-out.cogent $(VARIANT)/post-$*-expected.cogent

%-clean:
	-rm -f post-$*-out.cogent

