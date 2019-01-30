{-# LANGUAGE PackageImports #-}
module Gencot.Origin where
import "language-c" Language.C (NodeInfo,CNode,nodeInfo)
import Language.C.Data.Node (posOfNode,getLastTokenPos)
import Language.C.Data.Position (posRow)

data Origin = Origin { 
    sOfOrig :: [(NodeInfo,Bool)], 
    eOfOrig :: [(NodeInfo,Bool)] } deriving (Eq, Show)
noOrigin = Origin [] []

listOrigins :: CNode a => [a] -> [Origin]
listOrigins cs = foldr accu [] $ fmap nodeInfo cs 
    where accu :: NodeInfo -> [Origin] -> [Origin]
          accu n [] = [Origin [(n,True)] [(n,True)]]
          accu n ((Origin sn en):os) = 
            if (fstLine . fst . head) sn == lstLine n 
               then (Origin [(n,True)] []) : (Origin [] en) : os
               else (Origin [(n,True)] [(n,True)]) : (Origin sn en) : os

subOrigin :: CNode a => NodeInfo -> a -> Origin
subOrigin n c = Origin s e
    where s = if fstLine n == fstLine cn then [] else [(cn,True)]
          e = if lstLine n == lstLine cn then [] else [(cn,True)]
          cn = nodeInfo c

subListOrigins :: CNode a => NodeInfo -> [a] -> [Origin]
subListOrigins n [] = []
subListOrigins n (c:cs) = if null cs then [subOrigin n c] else o1r:osm ++ [onr]
    where o1r = if fstLine n == (fstLine . fst . head . sOfOrig) o1 then Origin (tail $ sOfOrig o1) (eOfOrig o1) else o1
          onr = if lstLine n == (lstLine . fst . last . eOfOrig) on then Origin (sOfOrig on) (init $ eOfOrig on) else on
          o1:osm = init os
          on = last os
          os = listOrigins (c:cs)

fstLine :: NodeInfo -> Int
fstLine = posRow . posOfNode

lstLine :: NodeInfo -> Int
lstLine = posRow . fst . getLastTokenPos


