{-# LANGUAGE PackageImports #-}
{-# LANGUAGE DeriveDataTypeable #-}
module Gencot.Origin where

import Data.Data (Data(..))
import Data.Maybe (catMaybes)

import "language-c" Language.C (NodeInfo,CNode,nodeInfo)
import Language.C.Data.Node (posOfNode,getLastTokenPos{- -},mkNodeInfoPosLen)
import Language.C.Data.Position (posRow,isSourcePos,Position{- -},retPos,initPos,)

data Origin = Origin { 
    sOfOrig :: [(Int,Bool)], 
    eOfOrig :: [(Int,Bool)] } deriving (Eq, Ord, Show, Data)
noOrigin = Origin [] []
mkOrigin n = unRepOrigin noRepOrig $ ownOrig n

type RepOrig = (Int,Int)
type OwnOrig = (Int,Int)
noRepOrig = (0,0)
noOwnOrig = (0,0)

ownOrig :: CNode a => a -> OwnOrig
ownOrig cn = (posLine $ fstPos n, posLine $ lstPos n)
    where n = nodeInfo cn

maybeOwnOrig :: (a -> OwnOrig) -> Maybe a -> OwnOrig
maybeOwnOrig = maybe noOwnOrig

mOwnOrig :: CNode a => Maybe a -> OwnOrig
mOwnOrig = maybeOwnOrig ownOrig

listOwnOrig :: (a -> OwnOrig) -> [a] -> OwnOrig
listOwnOrig _ [] = noOwnOrig
listOwnOrig f cs = (head $ foldr accOrigs [] (map fst ocs), head $ foldl (flip accOrigs) [] (map snd ocs))
    where ocs = map f cs

lOwnOrig :: CNode a => [a] -> OwnOrig
lOwnOrig = listOwnOrig ownOrig

pairOwnOrig :: (a -> OwnOrig) -> (b -> OwnOrig) -> (a,b) -> OwnOrig
pairOwnOrig fa fb (x,y) = listOwnOrig id [fa x, fb y]

tripOwnOrig :: (a -> OwnOrig) -> (b -> OwnOrig) -> (c -> OwnOrig) -> (a,b,c) -> OwnOrig
tripOwnOrig fa fb fc (x,y,z) = listOwnOrig id [fa x, fb y, fc z]

mkRepOrigs :: RepOrig -> [OwnOrig] -> [RepOrig]
mkRepOrigs (bef,aft) cs = 
    zip (reverse $ tail $ foldl (flip accOrigs) [bef] $ map snd cs) 
        (tail $ foldr accOrigs [aft] $ map fst cs)
    
accOrigs :: Int -> [Int] -> [Int]
accOrigs i [] = [i]
accOrigs i l@(i1:_) = if i == 0 then i1:l else i:l

unRepOrigin :: RepOrig -> OwnOrig -> Origin
unRepOrigin ro own = Origin s e
    where s = if fst own == 0 || fst own == fst ro then [] else [(fst own,True)]
          e = if snd own == 0 || snd own == snd ro then [] else [(snd own,True)]
          
uROrigin :: RepOrig -> NodeInfo -> Origin
uROrigin ro n = unRepOrigin ro $ ownOrig n

posLine :: Position -> Int
posLine p = if isSourcePos p then posRow p else 0

fstPos :: NodeInfo -> Position
fstPos = posOfNode

lstPos :: NodeInfo -> Position
lstPos = fst . getLastTokenPos

----------------------------------------------


testOrig = Origin [(2,True)] [(3,True)]
