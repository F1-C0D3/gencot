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

mkOrigin :: NodeInfo -> Origin
mkOrigin n = if hasPosition n then Origin [(n,True)] [(n,True)] else noOrigin

origin :: CNode a => a -> Origin
origin = mkOrigin . nodeInfo

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



listOrigins :: CNode a => [a] -> [Origin]
listOrigins cs = foldr accu [] $ fmap nodeInfo cs 
    where accu :: NodeInfo -> [Origin] -> [Origin]
          accu n [] = [mkOrigin n]
          accu n (hd@(Origin [] en):os) = (mkOrigin n) : hd : os
          accu n os | not $ hasPosition n = noOrigin : os -- maybe not correct, n may hide a repeat between its neighbours
          accu n (hd@(Origin sn en):os) = 
            if (fstLine . fst . head) sn == lstLine n 
               then (Origin [(n,True)] []) : (Origin [] en) : os
               else (mkOrigin n) : hd : os

subOrigin :: CNode a => NodeInfo -> a -> Origin
subOrigin n c | not $ hasPosition n = mkOrigin $ nodeInfo c
subOrigin n c | not $ hasPosition $ nodeInfo c = noOrigin
subOrigin n c = Origin s e 
    where s = if fstLine n == fstLine cn then [] else [(cn,True)]
          e = if lstLine n == lstLine cn then [] else [(cn,True)]
          cn = nodeInfo c

subListOrigins :: CNode a => NodeInfo -> [a] -> [Origin]
subListOrigins n [] = []
subListOrigins n os | not $ hasPosition n = listOrigins os
subListOrigins n (c:cs) = if null cs then [subOrigin n c] else o1r:osm ++ [onr]
    where o1r = if null $ sOfOrig o1 then o1 else 
                   if fstLine n == (fstLine . fst . head . sOfOrig) o1 
                      then Origin (tail $ sOfOrig o1) (eOfOrig o1) 
                      else o1
          onr = if null $ eOfOrig on then on else 
                   if lstLine n == (lstLine . fst . last . eOfOrig) on 
                      then Origin (sOfOrig on) (init $ eOfOrig on) 
                      else on
          o1:osm = init os
          on = last os
          os = listOrigins (c:cs)

sub1l1Origins :: (CNode a1, CNode a, CNode a2) => NodeInfo -> a1 -> [a] -> a2 -> (Origin,[Origin],Origin)
sub1l1Origins n x1 l x2 = (head h,init $ tail h,last h)
    where h = subListOrigins n ([nodeInfo x1] ++ (map nodeInfo l) ++ [nodeInfo x2])
sub2Origins :: (CNode a1, CNode a2) => NodeInfo -> a1 -> a2 -> (Origin,Origin)
sub2Origins n x1 x2 = (h!!0,h!!1)
    where h = subListOrigins n [nodeInfo x1, nodeInfo x2]

sub3Origins :: (CNode a1, CNode a2, CNode a3) => NodeInfo -> a1 -> a2 -> a3 -> (Origin,Origin,Origin)
sub3Origins n x1 x2 x3 = (h!!0,h!!1,h!!2)
    where h = subListOrigins n [nodeInfo x1, nodeInfo x2, nodeInfo x3]

subListMaybeOrigins :: CNode a => NodeInfo -> [Maybe a] -> [Maybe Origin]
subListMaybeOrigins n mxs = snd $ foldr addNothing ((subListOrigins n $ catMaybes mxs),[]) mxs
    where addNothing :: (Maybe a) -> ([Origin],[Maybe Origin]) -> ([Origin],[Maybe Origin])
          addNothing Nothing (os,mos) = (os,Nothing:mos)
          addNothing (Just _) (os,mos) = (init os,(Just $ last os):mos)

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
