#! /bin/csh

set s = test
set t = ${s}-$1
set G = ../../bin
set GS = ../../src
set M = src

cat $s.addincl $M/$s.h | $G/gencot-include include $M/$s.h  > $t.gi
$G/gencot-remcomments < $t.gi > $t.remc

$G/gencot-selpp < $t.remc > $t.pps
$G/gencot-selppconst $s.selppconsts < $t.pps > $t.ppconsts
$G/gencot-gendummydecls < $t.ppconsts > $t.dummydecls

$G/gencot-rempp $s.rempp-pat < $t.remc > $t.remp
$G/gencot-chsystem $s.chsystem < $t.remp | $G/gencot-cpp $t.dummydecls > $t.in
$GS/gencot-translate $s.h < $t.in > $t.out
$G/gencot-reporigs < $t.out > $t.op

$G/gencot-preppconst $s.omitconst < $t.pps > $t.preppconst
$G/gencot-prcppconst < $t.preppconst > $t.prcppconst
$G/gencot-mrgpp $t.prcppconst < $t.op > $t.ppconst

$G/gencot-remcomments < $M/$s.h > $t.remcf
$G/gencot-selpp < $t.remcf | $G/gencot-unline > $t.ppsf
$G/gencot-mrgppcond $t.ppsf < $t.ppconst > $t.ppcond

$G/gencot-selcomments < $M/$s.h > $t.comm
$G/gencot-mrgcomments $t.comm < $t.ppcond > $t.cogent
