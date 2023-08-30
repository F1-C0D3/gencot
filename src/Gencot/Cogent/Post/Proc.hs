{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Post.Proc where

import Gencot.Cogent.Ast (GenExpr,toRawExpr)
import Gencot.Cogent.Post.Util (ETrav)
import Gencot.Cogent.Post.Simplify (presimp,letproc,ifproc,opproc)
import Gencot.Cogent.Post.MatchTypes (boolproc, romodproc, bangproc, ebangproc, maynullproc)

postproc :: String -> GenExpr -> ETrav GenExpr
postproc tconf e = do
    let e1 = runpresimp tconf e
    e2 <- runtypes tconf e1
    return $ runsimp tconf e2

runpresimp :: String -> GenExpr -> GenExpr
runpresimp tconf e | elem 'p' tconf = e
runpresimp _ e = presimp e

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
    let e1 = boolproc' tconf e
    e2 <- romodproc' tconf e1
    e3 <- maynullproc' tconf e2
    e4 <- bangproc' tconf e3
    ebangproc' tconf e4

boolproc' :: String -> GenExpr -> GenExpr
boolproc' tconf e | elem 'r' tconf = e
boolproc' _ e = boolproc e

romodproc' :: String -> GenExpr -> ETrav GenExpr
romodproc' tconf e | elem 'r' tconf = return e
romodproc' _ e = romodproc e

bangproc' :: String -> GenExpr -> ETrav GenExpr
bangproc' tconf e | elem 'b' tconf = return e
bangproc' _ e = bangproc e

ebangproc' :: String -> GenExpr -> ETrav GenExpr
ebangproc' tconf e | elem 'e' tconf = return e
ebangproc' _ e = ebangproc e

maynullproc' :: String -> GenExpr -> ETrav GenExpr
maynullproc' tconf e | elem 'n' tconf = return e
maynullproc' _ e = maynullproc e
