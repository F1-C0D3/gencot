#! /bin/csh

../../bin/gencot-include src:include test.c < src/test.c > test-impl.gi
../../bin/gencot-remcomments < test-impl.gi > test-impl.remc

../../bin/gencot-selpp < test-impl.remc > test-impl.pps
../../bin/gencot-selppconst test.selppconsts < test-impl.pps > test-impl.ppconsts
../../bin/gencot-gendummydecls < test-impl.ppconsts > test-impl.dummydecls

../../bin/gencot-rempp test.rempp-pat < test-impl.remc > test-impl.remp
../../bin/gencot-cpp test-impl.dummydecls < test-impl.remp > test-impl.in
../../src/gencot-translate test.c < test-impl.in > test-impl.out
../../bin/gencot-reporigs < test-impl.out > test-impl.reporigs
../../bin/gencot-postproc < test-impl.reporigs > test-impl.op

../../bin/gencot-preppconst test.omitconst < test-impl.pps > test-impl.preppconst
../../bin/gencot-prcppconst < test-impl.preppconst > test-impl.prcppconst
../../bin/gencot-mrgpp test-impl.prcppconst < test-impl.op > test-impl.ppconst

../../bin/gencot-remcomments < src/test.c > test-impl.remcf
../../bin/gencot-selpp < test-impl.remcf | ../../bin/gencot-unline > test-impl.ppsf
../../bin/gencot-mrgppcond test-impl.ppsf < test-impl.ppconst > test-impl.ppcond

../../bin/gencot-selcomments < src/test.c > test-impl.comm
../../bin/gencot-mrgcomments test-impl.comm < test-impl.ppcond > test-impl.cogent


