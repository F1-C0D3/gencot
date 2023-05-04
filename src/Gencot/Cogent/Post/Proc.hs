{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Post.Proc where

import Gencot.Cogent.Ast (GenExpr,toRawExpr)
import Gencot.Cogent.Post.Simplify (letproc,ifproc,opproc)
import Gencot.Cogent.Post.MatchTypes (roproc,bangproc)

postproc :: String -> GenExpr -> GenExpr
postproc tconf e = runsimp tconf $ runtypes tconf e

runsimp :: String -> GenExpr -> GenExpr
runsimp tconf e = let e' = opproc' tconf $ ifproc' tconf $ letproc' tconf e
            in if toRawExpr e' == toRawExpr e
                  then e'
                  else runsimp tconf e'

letproc' tconf e | elem 'l' tconf = e
letproc' _ e = letproc e

ifproc' tconf e | elem 'f' tconf = e
ifproc' _ e = ifproc e

opproc' tconf e | elem 'o' tconf = e
opproc' _ e = opproc e

runtypes tconf e = bangproc' tconf $ roproc' tconf e

roproc' tconf e | elem 'r' tconf = e
roproc' _ e = roproc e

bangproc' tconf e | elem 'b' tconf = e
bangproc' _ e = bangproc e
