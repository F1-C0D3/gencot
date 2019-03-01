#! /bin/csh

../../bin/gencot-selcomments < src/test.c > test-impl.comm

../../bin/gencot-include src:include test.c < src/test.c \
  | ../../bin/gencot-remcomments > test-impl.remc

../../bin/gencot-selpp < test-impl.remc \
  | ../../bin/gencot-selppconst test.selppconsts \
  | ../../bin/gencot-gendummydecls > test-impl.dummydecls
  
../../bin/gencot-selpp < test-impl.remc \
  | ../../bin/gencot-preppconst test.omitconst \
  | ../../bin/gencot-prcppconst > test-impl.prcppconst

../../bin/gencot-remcomments < src/test.c \
  | ../../bin/gencot-selpp \
  | ../../bin/gencot-unline > test-impl.ppsf

../../bin/gencot-rempp test.rempp-pat < test-impl.remc \
  | ../../bin/gencot-cpp test-impl.dummydecls \
  | ../../src/gencot-translate test.c \
  | ../../bin/gencot-reporigs \
  | ../../bin/gencot-postproc \
  | ../../bin/gencot-mrgpp test-impl.prcppconst \
  | ../../bin/gencot-mrgppcond test-impl.ppsf \
  | ../../bin/gencot-mrgcomments test-impl.comm > test-impl.cogent

