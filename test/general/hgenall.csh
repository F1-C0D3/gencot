#! /bin/csh

../../bin/gencot-include include src/test.h < src/test.h > test-types.gi
../../bin/gencot-remcomments < test-types.gi > test-types.remc

../../bin/gencot-selpp < test-types.remc > test-types.pps
../../bin/gencot-selppconst test.selppconsts < test-types.pps > test-types.ppconsts
../../bin/gencot-gendummydecls < test-types.ppconsts > test-types.dummydecls

../../bin/gencot-rempp test.rempp-pat < test-types.remc > test-types.remp
../../bin/gencot-cpp test-types.dummydecls < test-types.remp > test-types.in
../../src/gencot-translate test.h < test-types.in > test-types.out
../../bin/gencot-reporigs < test-types.out > test-types.reporigs
../../bin/gencot-postproc < test-types.reporigs > test-types.op

../../bin/gencot-preppconst test.omitconst < test-types.pps > test-types.preppconst
../../bin/gencot-prcppconst < test-types.preppconst > test-types.prcppconst
../../bin/gencot-mrgpp test-types.prcppconst < test-types.op > test-types.ppconst

../../bin/gencot-remcomments < src/test.h > test-types.remcf
../../bin/gencot-selpp < test-types.remcf | ../../bin/gencot-unline > test-types.ppsf
../../bin/gencot-mrgppcond test-types.ppsf < test-types.ppconst > test-types.ppcond

../../bin/gencot-selcomments < src/test.h > test-types.comm
../../bin/gencot-mrgcomments test-types.comm < test-types.ppcond > test-types.cogent


