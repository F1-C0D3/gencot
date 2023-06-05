{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Post.Proc where

import Gencot.Cogent.Ast (GenExpr,toRawExpr)
import Gencot.Cogent.Post.Util (ETrav)
import Gencot.Cogent.Post.Simplify (letproc,ifproc,opproc)
import Gencot.Cogent.Post.MatchTypes (romodproc, bangproc)

postproc :: String -> GenExpr -> ETrav GenExpr
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

runtypes :: String -> GenExpr -> ETrav GenExpr
runtypes tconf e = do
    e1 <- romodproc' tconf e
    bangproc' tconf e1

romodproc' :: String -> GenExpr -> ETrav GenExpr
romodproc' tconf e | elem 'r' tconf = return e
romodproc' _ e = romodproc e

bangproc' :: String -> GenExpr -> ETrav GenExpr
bangproc' tconf e | elem 'b' tconf = return e
bangproc' _ e = bangproc e
