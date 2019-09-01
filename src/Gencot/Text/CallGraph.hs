{-# LANGUAGE PackageImports, TypeSynonymInstances, FlexibleInstances #-}
module Gencot.Text.CallGraph where

import Data.List as L (map,intercalate,sort)
import Data.Set as S (Set,toList,map)
import Data.Map as M (Map,unionWith,fromListWith,map,foldrWithKey)
import Data.Foldable (foldlM,find)
import Control.Monad (liftM,liftM2)

import Language.C.Analysis as LCA

import Gencot.Util.CallGraph (CallGraph,CGFunInvoke,CGInvoke(IdentInvoke,MemberInvoke))
import Gencot.Json.Identifier (getFunId,getLocalFunId,getFunMemberId)
 
-- | Translate a call graph to a relation on parmod function ids.
-- The second argument is the name of the main source file.
callGraphToIdentRel :: CallGraph -> String -> Set (String,String)
callGraphToIdentRel cg s = S.map (funInvokeToIdentRel s) cg

funInvokeToIdentRel :: String -> CGFunInvoke -> (String,String)
funInvokeToIdentRel s (fdef,(IdentInvoke idec _),False) = (getFunId fdef s,getFunId idec s)
funInvokeToIdentRel s (fdef,(IdentInvoke idec _),True) = (fid,getLocalFunId fid idec)
    where fid = getFunId fdef s
funInvokeToIdentRel s (fdef,(MemberInvoke ctyp mdec _),_) = (getFunId fdef s,getFunMemberId (LCA.sueRef ctyp) mdec)

-- | Convert a relation on Strings to the map from Strings to the pair
-- of predomain and postdomain, each represented as a String list.
prepareCallGraphMap :: Set (String,String) -> Map String ([String],[String])
prepareCallGraphMap rel = unionWith (\p1 p2 -> (fst p1,snd p2)) pre pst
    where pst = M.map (\l -> ([],l)) $ M.fromListWith (++) $ L.map (\(s1,s2) -> (s1,[s2])) $ toList rel
          pre = M.map (\l -> (l,[])) $ M.fromListWith (++) $ L.map (\(s1,s2) -> (s2,[s1])) $ toList rel

-- | Print a map from Strings to pre- and postdomain in a human readable form
printCallGraphMap :: Map String ([String],[String]) -> [String]
printCallGraphMap m = M.foldrWithKey printCallGraphFun [] m

printCallGraphFun :: String -> ([String],[String]) -> [String] -> [String]
printCallGraphFun key (pre,pst) acc =
    [key,"  from: " ++ (intercalate "," $ sort pre),"  to: " ++ (intercalate "," $ sort pst)] ++ acc
