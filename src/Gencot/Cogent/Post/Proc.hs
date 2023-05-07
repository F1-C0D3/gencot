{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Post.Proc where

import Gencot.Traversal (FTrav)
import Gencot.Cogent.Ast (GenExpr,toRawExpr)
import Gencot.Cogent.Post.Simplify (letproc,ifproc,opproc)
import Gencot.Cogent.Post.MatchTypes (roproc,bangproc)

postproc :: String -> GenExpr -> FTrav GenExpr
postproc tconf e = do
    e1 <- runtypes tconf e
    return $ runsimp tconf e1

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

runtypes :: String -> GenExpr -> FTrav GenExpr
runtypes tconf e = do
    e1 <- roproc' tconf e
    bangproc' tconf e1

roproc' :: String -> GenExpr -> FTrav GenExpr
roproc' tconf e | elem 'r' tconf = return e
roproc' _ e = roproc e

bangproc' :: String -> GenExpr -> FTrav GenExpr
bangproc' tconf e | elem 'b' tconf = return e
bangproc' _ e = bangproc e
