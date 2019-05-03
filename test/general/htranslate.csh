#! /bin/csh

set s = test
set t = ${s}-$1
set G = ../../bin
set GS = ../../src
set M = src

$G/gencot-selcomments < $M/$s.h > $t.comm

cat $s.gencot-addincl $M/$s.h \
  | $G/gencot-include ${M}:include $s.h \
  | $G/gencot-remcomments > $t.remc

$G/gencot-selpp < $t.remc \
  | $G/gencot-selppconst $s.gencot-manmacros > $t.ppconsts

$G/gencot-gendummydecls < $t.ppconsts > $t.dummydecls
  
$G/gencot-preppconst < $t.ppconsts \
  | $G/gencot-prcppconst > $t.prcppconst

$G/gencot-remcomments < $M/$s.h \
  | $G/gencot-selpp \
  | $G/gencot-unline > $t.ppsf

$G/gencot-prcppflags $s.gencot-manmacros < $t.ppsf > $t.prcppflags
$G/gencot-prcppincl < $t.ppsf > $t.prcppincl

$G/gencot-rempp $s.gencot-ppretain < $t.remc \
  | $G/gencot-chsystem $s.gencot-chsystem \
  | $G/gencot-cpp $t.dummydecls \
  | $GS/gencot-translate $s.h \
  | $G/gencot-reporigs \
  | $G/gencot-mrgpp $t.prcppconst \
  | $G/gencot-mrgpp $s.gencot-macrodefs \
  | $G/gencot-mrgpp $t.prcppflags \
  | $G/gencot-mrgpp $t.prcppincl \
  | $G/gencot-mrgppcond $t.ppsf \
  | $G/gencot-mrgcomments $t.comm > $t.cogent
