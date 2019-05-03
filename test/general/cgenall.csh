#! /bin/csh

set s = test
set t = ${s}
set G = ../../bin
set GS = ../../src
set M = src

cat common.gencot-addincl $M/$s.c | $G/gencot-include ${M}:include $s.c  > $t.gi
$G/gencot-remcomments < $t.gi > $t.remc

$G/gencot-selpp < $t.remc > $t.pps
$G/gencot-selppconst common.gencot-manmacros < $t.pps > $t.ppconsts
$G/gencot-gendummydecls < $t.ppconsts > $t.dummydecls

$G/gencot-rempp common.gencot-ppretain < $t.remc > $t.remp
$G/gencot-chsystem common.gencot-chsystem < $t.remp > $t.remps
$G/gencot-cpp common.gencot-macroconv $t.dummydecls < $t.remps > $t.in
$GS/gencot-translate $s.c < $t.in > $t.out
$G/gencot-reporigs < $t.out > $t.op

$G/gencot-preppconst < $t.ppconsts > $t.preppconst
$G/gencot-prcppconst < $t.preppconst > $t.prcppconst
$G/gencot-mrgpp $t.prcppconst < $t.op > $t.ppconst

$G/gencot-mrgpp $s.gencot-macrodefs < $t.ppconst > $t.ppmacros

$G/gencot-remcomments < $M/$s.c > $t.remcf
$G/gencot-selpp < $t.remcf | $G/gencot-unline > $t.ppsf
$G/gencot-prcppflags common.gencot-manmacros < $t.ppsf > $t.prcppflags
$G/gencot-mrgpp $t.prcppflags < $t.ppmacros > $t.ppflags
$G/gencot-prcppincl < $t.ppsf > $t.prcppincl
$G/gencot-mrgpp $t.prcppincl < $t.ppflags > $t.ppincl
$G/gencot-mrgppcond $t.ppsf < $t.ppincl > $t.ppcond

$G/gencot-selcomments < $M/$s.c > $t.comm
$G/gencot-mrgcomments $t.comm < $t.ppcond > $t.cogent
