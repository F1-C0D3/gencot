#! /bin/csh

set s = $1
set t = ${s}-$2
set G = ../../bin
set M = src
set I = include

if (-e $s.gencot-addincl) then
  cat common.gencot-addincl $s.gencot-addincl > .gencot-addincl
else
  cp common.gencot-addincl .gencot-addincl
endif
if (-e $s.gencot-manmacros) then
  cat common.gencot-manmacros $s.gencot-manmacros > .gencot-manmacros
else
  cp common.gencot-manmacros .gencot-manmacros
endif
if (-e $s.gencot-macroconv) then
  cat common.gencot-macroconv $s.gencot-macroconv > .gencot-macroconv
else
  cp common.gencot-macroconv .gencot-macroconv
endif
if (-e $s.gencot-ppretain) then
  cat common.gencot-ppretain $s.gencot-ppretain > .gencot-ppretain
else
  cp common.gencot-ppretain .gencot-ppretain
endif
if (-e $s.gencot-chsystem) then
  cat common.gencot-chsystem $s.gencot-chsystem > .gencot-chsystem
else
  cp common.gencot-chsystem .gencot-chsystem
endif

if ($s == "config") then 
  $G/gencot-preconfig < $M/$s.h > $t.gi
else
  cat .gencot-addincl $M/$s.h \
  | $G/gencot-include $I > $t.gi
endif

$G/gencot-remcomments < $t.gi > $t.remc

$G/gencot-selpp < $t.remc > $t.pps
$G/gencot-selppconst .gencot-manmacros < $t.pps > $t.ppconsts
$G/gencot-gendummydecls < $t.ppconsts > $t.dummydecls

$G/gencot-rempp .gencot-ppretain < $t.remc > $t.remp
$G/gencot-chsystem .gencot-chsystem < $t.remp > $t.remps
$G/gencot-cpp .gencot-macroconv  $t.dummydecls < $t.remps > $t.in
$G/gencot-translate $s.h < $t.in > $t.out
$G/gencot-reporigs < $t.out > $t.op

$G/gencot-deccomments < $t.in > $t.decmarks

$G/gencot-preppconst < $t.ppconsts > $t.preppconst
$G/gencot-prcppconst < $t.preppconst > $t.prcppconst
$G/gencot-mrgpp $t.prcppconst < $t.op > $t.ppconst
$G/gencot-mrgpp $s.gencot-macrodefs < $t.ppconst > $t.ppmacros

if ($s == "config") then 
  cp $t.remc $t.remcf
else
  $G/gencot-remcomments < $M/$s.h > $t.remcf
endif

$G/gencot-selpp < $t.remcf | $G/gencot-unline > $t.ppsf
$G/gencot-prcppflags .gencot-manmacros < $t.ppsf > $t.prcppflags
$G/gencot-mrgpp $t.prcppflags < $t.ppmacros > $t.ppflags
$G/gencot-prcppincl < $t.ppsf > $t.prcppincl
$G/gencot-mrgpp $t.prcppincl < $t.ppflags > $t.ppincl
$G/gencot-mrgppcond $t.ppsf < $t.ppincl > $t.ppcond


if ($s == "config") then 
  $G/gencot-preconfig < $M/$s.h \
  | $G/gencot-selcomments > $t.comm
  $G/gencot-postconfig $M/$s.h < $t.ppcond \
  | $G/gencot-mrgcomments $t.comm  > $t.cogent
else
  $G/gencot-selcomments < $M/$s.h > $t.comm
  $G/gencot-mrgcomments $t.comm < $t.ppcond > $t.cogent
endif

if (! -e comments) mkdir comments
(cd comments; ../$G/gencot-movcomments ../$t.comm < ../$t.decmarks)

rm .gencot-addincl .gencot-manmacros .gencot-macroconv .gencot-ppretain .gencot-chsystem

