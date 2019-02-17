#! /bin/csh

../../bin/gencot-include src:include test.c < src/test.c > test.cgi
../../bin/gencot-remcomments < test.cgi > test.cremc

../../bin/gencot-selpp < test.cremc > test.cpps
../../bin/gencot-selppconst test.cselppconsts < test.cpps > test.cppconsts
../../bin/gencot-gendummydecls < test.cppconsts > test.cdummydecls

../../bin/gencot-rempp test.hrempp-pat < test.cremc > test.cremp
../../bin/gencot-cpp test.cdummydecls < test.cremp > test.ci
../../src/gencot-translate test.c < test.ci > test.co
../../bin/gencot-postproc < test.co > test.cop

../../bin/gencot-remcomments < src/test.c > test.cremcf
../../bin/gencot-selpp < test.cremcf > test.cppsf
../../bin/gencot-mrgppcond test.cppsf < test.cop > test.cppcond

../../bin/gencot-selcomments < src/test.c > test.ccomm
../../bin/gencot-mrgcomments test.ccomm < test.cppcond > test-impl.cogent


