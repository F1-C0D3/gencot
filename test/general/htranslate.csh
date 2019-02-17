#! /bin/csh

../../bin/gencot-selcomments < src/test.h > test.hcomm

../../bin/gencot-include include src/test.h < src/test.h \
  | ../../bin/gencot-remcomments > test.hremc
  
../../bin/gencot-selpp < test.hremc \
  | ../../bin/gencot-selppconst test.hselppconsts \
  | ../../bin/gencot-gendummydecls > test.hdummydecls
  
../../bin/gencot-remcomments < src/test.h \
  | ../../bin/gencot-selpp > test.hppsf

../../bin/gencot-rempp test.hrempp-pat < test.hremc \
  | ../../bin/gencot-cpp test.hdummydecls \
  | ../../src/gencot-translate test.h \
  | ../../bin/gencot-postproc \
  | ../../bin/gencot-mrgppcond test.hppsf \
  | ../../bin/gencot-mrgcomments test.hcomm > test-types.cogent

