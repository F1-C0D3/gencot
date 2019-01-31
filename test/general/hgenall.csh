#! /bin/csh

../../bin/gencot-include include < src/test.h > test.hgi
../../bin/gencot-remcomments < test.hgi > test.hremc
../../bin/gencot-rempp test.hrempp-pat < test.hremc > test.hremp
../../bin/gencot-cpp < test.hremp > test.hi++
../../bin/gencot-remc++ < test.hi++ > test.hi
../../src/gencot-translate test.h < test.hi > test.ho
../../bin/gencot-postproc < test.ho > test.hop
../../bin/gencot-selcomments < src/test.h > test.hcomm
../../bin/gencot-mrgcomments test.hcomm < test.hop > test-types.cogent


