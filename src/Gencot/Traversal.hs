{-# LANGUAGE PackageImports #-}
{-# LANGUAGE DeriveDataTypeable #-}
module Gencot.Traversal where

import Gencot.Origin

import "language-c" Language.C (NodeInfo,CNode,nodeInfo)
import Language.C.Data.Node (posOfNode,getLastTokenPos{- -},mkNodeInfoPosLen)
import Language.C.Data.Position (posRow,isSourcePos,Position{- -},retPos,initPos,)

import Language.C.Analysis.TravMonad (Trav, modifyUserState, getUserState)

type OTrav = Trav [[RepOrig]]

-- Achtung: immer mit [[noRepOrig]] initialisieren, damit erstes pushSubRepOrigs funktioniert!

getNOrigin :: NodeInfo -> OTrav Origin
getNOrigin n = do
    ((ro:_):_) <- getUserState
    return $ uROrigin ro n

getOrigin :: OwnOrig -> OTrav Origin
getOrigin oo = do
    ((ro:_):_) <- getUserState
    return $ unRepOrigin ro oo

pushOrigs :: [OwnOrig] -> OTrav ()
pushOrigs os = do
    ((ro:_):_) <- getUserState
    modifyUserState (\rostack -> (mkRepOrigs ro os) : rostack)

nextOrig :: OTrav ()
nextOrig = do
    modifyUserState (\(ros:rostack) -> if null (tail ros) then rostack else (tail ros):rostack)
    
popOrigs :: OTrav ()
popOrigs = do
    modifyUserState (\(_:rostack) -> rostack)

useOrig :: (a -> OTrav b) -> a -> OTrav b
useOrig trans c = do 
    r <- trans c 
    nextOrig 
    return r

mapOrigs :: (a -> OTrav b) -> [a] -> OTrav [b]
mapOrigs trans cs =
    mapM (\a -> do { r <- trans a; nextOrig; return r }) cs

optOrig :: (a -> OTrav b) -> (Maybe a) -> OTrav (Maybe b)
optOrig trans mc = 
    mapM (\a -> do { r <- trans a; nextOrig; return r }) mc

    
