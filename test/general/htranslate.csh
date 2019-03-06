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
  | ../../bin/gencot-chsystem test.chsystem \
  | ../../bin/gencot-cpp test-types.dummydecls \
  | ../../src/gencot-translate test.h \
  | ../../bin/gencot-reporigs \
  | ../../bin/gencot-mrgpp test-types.prcppconst \
  | ../../bin/gencot-mrgppcond test-types.ppsf \
  | ../../bin/gencot-mrgcomments test-types.comm > test-types.cogent

set s = test
set t = ${s}-$1
set G = ../../bin
set GS = ../../src
set M = src

$G/gencot-selcomments < $M/$s.h > $t.comm

cat $s.addincl $M/$s.h
  | $G/gencot-include ${M}:include $s.h \
  | $G/gencot-remcomments > $t.remc

$G/gencot-selpp < $t.remc \
  | $G/gencot-selppconst $s.selppconsts \
  | $G/gencot-gendummydecls > $t.dummydecls
  
$G/gencot-selpp < $t.remc \
  | $G/gencot-preppconst $s.omitconst \
  | $G/gencot-prcppconst > $t.prcppconst

$G/gencot-remcomments < $M/$s.h \
  | $G/gencot-selpp \
  | $G/gencot-unline > $t.ppsf

$G/gencot-rempp $s.rempp-pat < $t.remc \
  | $G/gencot-chsystem $s.chsystem \
  | $G/gencot-cpp $t.dummydecls \
  | $GS/gencot-translate $s.h \
  | $G/gencot-reporigs \
  | $G/gencot-mrgpp $t.prcppconst \
  | $G/gencot-mrgppcond $t.ppsf \
  | $G/gencot-mrgcomments $t.comm > $t.cogent
