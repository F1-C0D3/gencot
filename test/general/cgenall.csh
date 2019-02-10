#! /bin/csh

../../bin/gencot-include src:include < src/test.c > test.cgi
../../bin/gencot-remcomments < test.cgi > test.cremc

../../bin/gencot-selpp < test.cremc > test.cpps
../../bin/gencot-selppconst test.cselppconsts < test.cpps > test.cppconsts
../../bin/gencot-gendummydecls < test.cppconsts > test.cdummydecls

../../bin/gencot-rempp test.hrempp-pat < test.cremc > test.cremp
#../../bin/gencot-cpp < test.cremp > test.ci #++
cpp -include test.cdummydecls < test.cremp > test.ci #++
#../../bin/gencot-remc++ < test.ci++ > test.ci
../../src/gencot-translate test.c < test.ci > test.co
../../bin/gencot-postproc < test.co > test.cop
../../bin/gencot-selcomments < src/test.c > test.ccomm
../../bin/gencot-mrgcomments test.ccomm < test.cop > test-impl.cogent


