#! /bin/csh

../../bin/gencot-selcomments < src/test.c > test.ccomm

../../bin/gencot-include src:include test.c < src/test.c \
  | ../../bin/gencot-remcomments > test.cremc

../../bin/gencot-selpp < test.cremc \
  | ../../bin/gencot-selppconst test.cselppconsts \
  | ../../bin/gencot-gendummydecls > test.cdummydecls
  
../../bin/gencot-remcomments < src/test.c \
  | ../../bin/gencot-selpp > test.cppsf

../../bin/gencot-rempp test.hrempp-pat < test.cremc \
  | ../../bin/gencot-cpp test.cdummydecls \
  | ../../src/gencot-translate test.c \
  | ../../bin/gencot-postproc \
  | ../../bin/gencot-mrgppcond test.cppsf \
  | ../../bin/gencot-mrgcomments test.ccomm > test-impl.cogent

