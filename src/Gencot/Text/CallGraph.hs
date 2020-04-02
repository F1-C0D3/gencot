{-# LANGUAGE PackageImports, TypeSynonymInstances, FlexibleInstances #-}
module Gencot.Text.CallGraph where

import Data.List as L (map,intercalate,sort,isInfixOf)
import Data.Set as S (Set,toList,map)
import Data.Map as M (Map,unionWith,fromListWith,map,foldrWithKey)
import Data.Foldable (foldlM,find)
import Control.Monad (liftM,liftM2)

import Language.C.Analysis as LCA
import Language.C.Data.Ident as LCI

import Gencot.Util.CallGraph (CallGraph,CGFunInvoke,CGInvoke(IdentInvoke,MemberInvoke))
import Gencot.Items.Types (getIndividualItemId,getTagItemId,getParamSubItemId,getMemberSubItemId,getFunctionSubItemId)
import Gencot.Items.Identifier (paramSubItemId) -- only temporary
 
-- | Translate a call graph to a relation on parmod function ids.
-- The second argument is the name of the main source file.
callGraphToIdentRel :: CallGraph -> String -> Set (String,String)
callGraphToIdentRel cg s = S.map (funInvokeToIdentRel s) cg

funInvokeToIdentRel :: String -> CGFunInvoke -> (String,String)
funInvokeToIdentRel s (fdef,(IdentInvoke idec _),False) = 
    (getIndividualItemId (LCA.FunctionDef fdef) s,getFunctionSubItemId (LCA.declType idec) $ getIndividualItemId idec s )
funInvokeToIdentRel s (fdef,(IdentInvoke idec _),True) = (fid,getFunctionSubItemId (LCA.declType idec) pid)
    where fid = getIndividualItemId (LCA.FunctionDef fdef) s
          pid = -- getParamSubItemId fid (pos,pdec) -- use when pos and pdec are available
                paramSubItemId fid 0 $ LCI.identToString $ LCA.declIdent idec

funInvokeToIdentRel s (fdef,(MemberInvoke (LCA.CompType sueref knd _ _ _) mdec _),_) = 
    (getIndividualItemId (LCA.FunctionDef fdef) s,
     getFunctionSubItemId (LCA.declType mdec) $ getMemberSubItemId (getTagItemId sueref knd) mdec)

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
