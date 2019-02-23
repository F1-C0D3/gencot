#! /bin/csh

../../bin/gencot-selcomments < src/test.h > test-types.comm

../../bin/gencot-include include src/test.h < src/test.h \
  | ../../bin/gencot-remcomments > test-types.remc
  
../../bin/gencot-selpp < test-types.remc \
  | ../../bin/gencot-selppconst test.selppconsts \
  | ../../bin/gencot-gendummydecls > test-types.dummydecls
  
../../bin/gencot-selpp < test-types.remc \
  | ../../bin/gencot-preppconst test.omitconst \
  | ../../bin/gencot-prcppconst > test-types.prcppconst

../../bin/gencot-remcomments < src/test.h \
  | ../../bin/gencot-selpp \
  | ../../bin/gencot-unline > test-types.ppsf

../../bin/gencot-rempp test.rempp-pat < test-types.remc \
  | ../../bin/gencot-cpp test-types.dummydecls \
  | ../../src/gencot-translate test.h \
  | ../../bin/gencot-postproc \
  | ../../bin/gencot-mrgpp test-types.prcppconst \
  | ../../bin/gencot-mrgppcond test-types.ppsf \
  | ../../bin/gencot-mrgcomments test-types.comm > test-types.cogent

