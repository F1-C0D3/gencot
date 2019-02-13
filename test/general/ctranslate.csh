#! /bin/csh

../../bin/gencot-selcomments < src/test.c > test.ccomm
../../bin/gencot-include src:include test.c < src/test.c \
  | ../../bin/gencot-remcomments | ../../bin/gencot-rempp test.hrempp-pat \
  | ../../bin/gencot-cpp | ../../bin/gencot-remc++ \
  | ../../src/gencot-translate test.c | ../../bin/gencot-postproc \
  | ../../bin/gencot-mrgcomments test.ccomm > test-impl.cogent

