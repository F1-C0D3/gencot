#! /bin/csh

../../bin/gencot-selcomments < src/test.h > test.hcomm
../../bin/gencot-include include < src/test.h \
  | ../../bin/gencot-remcomments | ../../bin/gencot-rempp test.hrempp-pat \
  | ../../bin/gencot-cpp | ../../bin/gencot-remc++ \
  | ../../src/gencot-translate test.h | ../../bin/gencot-postproc \
  | ../../bin/gencot-mrgcomments test.hcomm > test-types.cogent

