#! /bin/csh

set s = test
set t = ${s}-$1
set G = ../../bin
set GS = ../../src
set M = src

cat $s.addincl $M/$s.c | $G/gencot-include ${M}:include $s.c  > $t.gi
$G/gencot-remcomments < $t.gi > $t.remc

$G/gencot-selpp < $t.remc > $t.pps
$G/gencot-selppconst $s.gencot-manmacros < $t.pps > $t.ppconsts
$G/gencot-gendummydecls < $t.ppconsts > $t.dummydecls

$G/gencot-rempp $s.gencot-ppretain < $t.remc > $t.remp
$G/gencot-chsystem $s.chsystem < $t.remp > $t.remps
$G/gencot-cpp $t.dummydecls < $t.remps > $t.in
$GS/gencot-translate $s.c < $t.in > $t.out
$G/gencot-reporigs < $t.out > $t.op

$G/gencot-preppconst < $t.ppconsts > $t.preppconst
$G/gencot-prcppconst < $t.preppconst > $t.prcppconst
$G/gencot-mrgpp $t.prcppconst < $t.op > $t.ppconst

$G/gencot-remcomments < $M/$s.c > $t.remcf
$G/gencot-selpp < $t.remcf | $G/gencot-unline > $t.ppsf
$G/gencot-mrgppcond $t.ppsf < $t.ppconst > $t.ppcond

$G/gencot-selcomments < $M/$s.c > $t.comm
$G/gencot-mrgcomments $t.comm < $t.ppcond > $t.cogent
