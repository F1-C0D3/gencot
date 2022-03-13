{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Postproc where

import Gencot.Cogent.Ast (GenExpr,toRawExpr)
import Gencot.Cogent.Simplify (letproc,ifproc,opproc)
 
postproc :: GenExpr -> GenExpr
postproc e = runsimp e

runsimp :: GenExpr -> GenExpr
runsimp e = let e' = opproc $ ifproc $ letproc e
            in if toRawExpr e' == toRawExpr e
                  then e'
                  else runsimp e'
