{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Postproc where

import Gencot.Cogent.Ast (GenExpr,toRawExpr)
import Gencot.Cogent.Simplify (letproc,ifproc,opproc)
 
postproc :: String -> GenExpr -> GenExpr
postproc tconf e = runsimp tconf e

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
