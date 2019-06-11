#! /bin/csh

set s = $1
set t = ${s}-$2
rm $t.gi
rm $t.remc
rm $t.pps
rm $t.ppconsts
rm $t.dummydecls
rm $t.remp
rm $t.remps
rm $t.in
rm $t.out
rm $t.op
rm $t.preppconst
rm $t.prcppconst
rm $t.ppconst
rm $t.ppmacros
rm $t.remcf
rm $t.ppsf
rm $t.prcppflags
rm $t.ppflags
rm $t.prcppincl
rm $t.ppincl
rm $t.ppcond
rm $t.comm
rm $t.decmarks

