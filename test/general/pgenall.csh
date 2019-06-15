#! /bin/csh

set s = test
set p = package
set t = ${s}
set G = ../../bin
set M = src

cat common.gencot-addincl $M/$s.c | $G/gencot-include ${M}:include > $t.gi
$G/gencot-remcomments < $t.gi > $t.remc

$G/gencot-selpp < $t.remc > $t.pps
$G/gencot-selppconst common.gencot-manmacros < $t.pps > $t.ppconsts
$G/gencot-gendummydecls < $t.ppconsts > $t.dummydecls

$G/gencot-rempp common.gencot-ppretain < $t.remc > $t.remp
$G/gencot-chsystem common.gencot-chsystem < $t.remp > $t.remps
$G/gencot-cpp common.gencot-macroconv $t.dummydecls < $t.remps > $t.in

$G/gencot-extfuns $s.c < $t.in > $p-exit.out
$G/gencot-reporigs < $p-exit.out > $p-exit.op
$G/gencot-mrgcomments /dev/null < $p-exit.op > $p-exit.cogent
