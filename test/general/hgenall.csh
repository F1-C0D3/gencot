#! /bin/csh

../../bin/gencot-include include src/test.h < src/test.h > test.hgi
../../bin/gencot-remcomments < test.hgi > test.hremc

../../bin/gencot-selpp < test.hremc > test.hpps
../../bin/gencot-selppconst test.hselppconsts < test.hpps > test.hppconsts
../../bin/gencot-gendummydecls < test.hppconsts > test.hdummydecls

../../bin/gencot-rempp test.hrempp-pat < test.hremc > test.hremp
../../bin/gencot-cpp test.hdummydecls < test.hremp > test.hi
../../src/gencot-translate test.h < test.hi > test.ho
../../bin/gencot-postproc < test.ho > test.hop

../../bin/gencot-remcomments < src/test.h > test.hremcf
../../bin/gencot-selpp < test.hremcf | ../../bin/gencot-unline > test.hppsf
../../bin/gencot-mrgppcond test.hppsf < test.hop > test.hppcond

../../bin/gencot-selcomments < src/test.h > test.hcomm
../../bin/gencot-mrgcomments test.hcomm < test.hppcond > test-types.cogent


