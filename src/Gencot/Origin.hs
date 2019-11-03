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

mkBegSignedOrigin :: Bool -> NodeInfo -> Origin
mkBegSignedOrigin s n = if hasPosition n then Origin [(n,s)] [] else noOrigin

mkEndSignedOrigin :: Bool -> NodeInfo -> Origin
mkEndSignedOrigin s n = if hasPosition n then Origin [] [(n,s)] else noOrigin

mkBegOrigin = mkBegSignedOrigin True
mkEndOrigin = mkEndSignedOrigin True

prepSignedOrigin :: Bool -> NodeInfo -> Origin -> Origin
prepSignedOrigin sgn n (Origin s e) = Origin ((n,sgn):s) e

appdSignedOrigin :: Bool -> NodeInfo -> Origin -> Origin
appdSignedOrigin sgn n (Origin s e) = Origin s (e++[(n,sgn)])

prepOrigin = prepSignedOrigin True
appdOrigin = appdSignedOrigin True

toNoComOrigin :: Origin -> Origin
toNoComOrigin (Origin s e) = Origin (map toNoCom s) (map toNoCom e)

toNoCom :: (NodeInfo,Bool) -> (NodeInfo, Bool)
toNoCom (n,_) = (n,False)

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

isNested :: NodeInfo -> NodeInfo -> Bool
isNested n1 n2 =
    hasPosition n1 && hasPosition n2 && (fstLine n1 >= fstLine n2) && (lstLine n1 <= lstLine n2)

testpos1 = retPos $ initPos "<stdin>"
testpos2 = retPos testpos1
testnode = mkNodeInfoPosLen testpos1 (testpos2,0)
testOrig = Origin [(testnode,True)] [(testnode,True)]
