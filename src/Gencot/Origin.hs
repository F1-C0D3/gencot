{-# LANGUAGE PackageImports #-}
{-# LANGUAGE DeriveDataTypeable #-}
module Gencot.Origin where

import Data.Data (Data(..))
import Data.Maybe (catMaybes)

import "language-c" Language.C (NodeInfo,CNode,nodeInfo)
import Language.C.Data.Node (posOfNode,getLastTokenPos{- -},mkNodeInfoPosLen)
import Language.C.Data.Position (posRow,isSourcePos{- -},retPos,initPos,)

data Origin = Origin { 
    sOfOrig :: [(NodeInfo,Bool)], 
    eOfOrig :: [(NodeInfo,Bool)] } deriving (Eq, Ord, Show, Data)
noOrigin = Origin [] []

isBegOrigin :: Origin -> Bool
isBegOrigin (Origin [] _) = False
isBegOrigin _ = True

isEndOrigin :: Origin -> Bool
isEndOrigin (Origin _ []) = False
isEndOrigin _ = True

mkSignedOrigin :: Bool -> NodeInfo -> Origin
mkSignedOrigin s n = if hasPosition n then Origin [(n,s)] [(n,s)] else noOrigin

mkOrigin = mkSignedOrigin True
mkNoComOrigin = mkSignedOrigin False

origin :: CNode a => a -> Origin
origin = mkOrigin . nodeInfo

noComOrigin :: CNode a => a -> Origin
noComOrigin = mkNoComOrigin . nodeInfo

maybeOrigin :: (a -> Origin) -> Maybe a -> Origin
maybeOrigin = maybe noOrigin

listOrigin :: (a -> Origin) -> [a] -> Origin
listOrigin f cs = 
    Origin bs es
    where 
        bs = if null bcs then [] else [((fst.head.sOfOrig.head) bcs, True)]
        es = if null ecs then [] else [((fst.head.eOfOrig.last) ecs, True)]
        bcs = filter isBegOrigin ocs
        ecs = filter isEndOrigin ocs
        ocs = map f cs

pairOrigin :: (a -> Origin) -> (b -> Origin) -> (a,b) -> Origin
pairOrigin fa fb (x,y) = listOrigin id [fa x, fb y]

fstLine :: NodeInfo -> Int
fstLine = posRow . posOfNode

lstLine :: NodeInfo -> Int
lstLine = posRow . fst . getLastTokenPos

hasPosition :: NodeInfo -> Bool
hasPosition n = (isSourcePos $ posOfNode n) && (isSourcePos $ fst $ getLastTokenPos n) 

testpos1 = retPos $ initPos "<stdin>"
testpos2 = retPos testpos1
testnode = mkNodeInfoPosLen testpos1 (testpos2,0)
testOrig = Origin [(testnode,True)] [(testnode,True)]
