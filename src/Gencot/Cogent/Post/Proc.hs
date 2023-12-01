{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Post.Proc where

import Gencot.Cogent.Ast (GenExpr,toRawExpr)
import Gencot.Cogent.Post.Util (ETrav)
import Gencot.Cogent.Post.Simplify (presimp, letproc, ifproc, opproc)
import Gencot.Cogent.Post.MatchTypes (boolproc, intproc, bangproc, ebangproc, maynullproc)
import Gencot.Cogent.Post.TakePut (tpproc)
import Gencot.Cogent.Post.Misc (romodproc, opnullproc)

postproc :: String -> GenExpr -> ETrav GenExpr
postproc tconf e = do
    let e1 = runpresimp tconf e
    e2 <- runtypes tconf e1
    e3 <- tpproc' tconf $ opnullproc' tconf e2
    return $ runsimp tconf e3

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
    e1 <- romodproc' tconf e
    e2 <- boolproc' tconf e1
    e3 <- maynullproc' tconf e2
    e4 <- bangproc' tconf e3
    e5 <- ebangproc' tconf e4
    intproc' tconf e5

boolproc' :: String -> GenExpr -> ETrav GenExpr
boolproc' tconf e | elem 'c' tconf = return e
boolproc' _ e = boolproc e

intproc' :: String -> GenExpr -> ETrav GenExpr
intproc' tconf e | elem 'i' tconf = return e
intproc' _ e = intproc e

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

opnullproc' :: String -> GenExpr -> GenExpr
opnullproc' tconf e | elem 'm' tconf = e
opnullproc' _ e = opnullproc e

tpproc' :: String -> GenExpr -> ETrav GenExpr
tpproc' tconf e | elem 't' tconf = return e
tpproc' _ e = tpproc e
