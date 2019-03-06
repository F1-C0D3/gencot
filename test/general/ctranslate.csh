#! /bin/csh

set s = test
set t = ${s}-$1
set G = ../../bin
set GS = ../../src
set M = src

$G/gencot-selcomments < $M/$s.c > $t.comm

cat $s.addincl $M/$s.c
  | $G/gencot-include ${M}:include $s.c \
  | $G/gencot-remcomments > $t.remc

$G/gencot-selpp < $t.remc \
  | $G/gencot-selppconst $s.selppconsts \
  | $G/gencot-gendummydecls > $t.dummydecls
  
$G/gencot-selpp < $t.remc \
  | $G/gencot-preppconst $s.omitconst \
  | $G/gencot-prcppconst > $t.prcppconst

$G/gencot-remcomments < $M/$s.c \
  | $G/gencot-selpp \
  | $G/gencot-unline > $t.ppsf

$G/gencot-rempp $s.rempp-pat < $t.remc \
  | $G/gencot-chsystem $s.chsystem \
  | $G/gencot-cpp $t.dummydecls \
  | $GS/gencot-translate $s.c \
  | $G/gencot-reporigs \
  | $G/gencot-mrgpp $t.prcppconst \
  | $G/gencot-mrgppcond $t.ppsf \
  | $G/gencot-mrgcomments $t.comm > $t.cogent

