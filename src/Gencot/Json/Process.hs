{-# LANGUAGE PackageImports, TypeSynonymInstances, FlexibleInstances #-}

-- | Process JSON function descriptions.
module Gencot.Json.Process where

import qualified Data.Set as S (Set,toList,fromList,difference,singleton,foldr,union,insert,empty)
import Data.List (find,isSuffixOf,isPrefixOf,nub)
import qualified Data.Map.Strict as M (Map,unions,unionsWith,unionWith,empty,singleton,foldr,map,fromList,elems,notMember,keys)
import Data.Map.Strict ((!))
import Data.Maybe (mapMaybe,isJust,fromJust,catMaybes)
import Data.Char (isDigit)
import Text.JSON

import Gencot.Json.Parmod (Parmod,Parmods)

qmark = showJSON "?"
jsEmpty = JSArray []

showRemainingPars :: Parmods -> [String]
showRemainingPars parmods =
    map showPar $ getFunAttrs isRemainingPar parmods
    where showPar (fun,par,mod) = fun ++ "/" ++ par

-- | From a function description sequence retrieve all function attributes satisfying a predicate.
-- The predicate is applied to all attributes of all function descriptions.
-- The resulting list contains triples of function name, attribute name and attribute value
getFunAttrs :: ((String,String,JSValue) -> Bool) -> Parmods -> [(String,String,JSValue)]
getFunAttrs pred parmods = concatMap (getFAttrs pred) parmods

getFAttrs :: ((String,String,JSValue) -> Bool) -> Parmod -> [(String,String,JSValue)]
getFAttrs pred jso = mapMaybe (selAttr pred) $ attrs
    where attrs = map (\(nam,val) -> (fnam,nam,val)) $ fromJSObject jso
          fnam = getFunName jso

getFunName :: Parmod -> String
getFunName jso = case valFromObj "f_name" jso of
                      Ok s -> s
                      Error msg -> error $ "Name not found in function description:\n" ++ encode jso ++ "\n" ++ msg

getFunNumPars :: Parmod -> JSValue
getFunNumPars jso = case valFromObj "f_num_params" jso of
                      Ok s -> s
                      Error msg -> error $ "Number of parameters not found in function description:\n" ++ encode jso ++ "\n" ++ msg

getFunResult :: Parmod -> String
getFunResult jso = case valFromObj "f_result" jso of
                      Ok s -> s
                      Error msg -> ""

selAttr :: ((String,String,JSValue) -> Bool) -> (String,String,JSValue) -> Maybe (String,String,JSValue)
selAttr pred attr = if pred attr then Just attr else Nothing

isRemainingPar :: (String,String,JSValue) -> Bool
isRemainingPar (_,nam,val) | isDigit $ head nam =
    case val of
         JSString jstr -> '?' == (head $ fromJSString jstr)
         _ -> False
isRemainingPar _ = False

showRequired  :: Parmods -> [String]
showRequired parmods =
    map showReq $ getRequired parmods
    where showReq req = "  " ++ req

-- | Get the required invocations from a function description sequence.
-- This are all invocations on which a parameter depends which is specified as dependent, 
-- where the invocation is not described in the sequence.
-- The result is the list of the names of all such invocations, without duplicates.
getRequired :: Parmods -> [String]
getRequired parmods = S.toList $ S.difference (S.fromList $ map (getInvokeName . snd) $ ri) fn
    where dp = getFunAttrs isDependentPar parmods
          ri = filter (isRequiredInvoke dp) $ getInvokes parmods
          fn = S.fromList $ map (\(f,_,_) -> f) $ getFunAttrs isFunName parmods
          
getInvokeName :: JSObject JSValue -> String
getInvokeName jso = case valFromObj "name" jso of
                      Ok s -> s
                      Error msg -> error $ "Name not found in invocation description:\n" ++ encode jso ++ "\n" ++ msg
          
isDependentPar :: (String,String,JSValue) -> Bool
isDependentPar (_,nam,val) | isDigit $ head nam =
    case val of
         JSString jstr -> "depends" == fromJSString jstr
         _ -> False
isDependentPar _ = False

-- | Get all invocations from a sequence of function descriptions.
-- The result is a list of pairs (f,i) where f is the function name of the function invoking i.
getInvokes :: Parmods -> [(String,JSObject JSValue)]
getInvokes parmods = concatMap getFunInvokes $ getFunAttrs isInvokes parmods

getFunInvokes :: (String,String,JSValue) -> [(String,JSObject JSValue)]
getFunInvokes (fnam,_,val) =
    case readJSON val of
         Ok a -> map (\jso -> (fnam,jso)) a
         Error msg -> error $ "Cannot read invocations of " ++ fnam ++ " as a list of JSON objects.\n"
                            ++ msg

isFunName :: (String,String,JSValue) -> Bool
isFunName (_,"f_name",_) = True
isFunName _ = False

isInvokes :: (String,String,JSValue) -> Bool
isInvokes (_,"f_invocations",_) = True
isInvokes _ = False

isParam :: (String,String,JSValue) -> Bool
isParam (_,nam,_) = isDigit $ head nam

isRequiredInvoke :: [(String,String,JSValue)] -> (String,JSObject JSValue) -> Bool
isRequiredInvoke dp (fnam,jso) = 
    any (hasDepend dp) $ fromJSObject jso
    where hasDepend :: [(String,String,JSValue)] -> (String,JSValue) -> Bool
          hasDepend dp (nam,val) | isDigit $ head nam = 
              case (readJSON val) :: Result [String] of 
                   Ok deps -> any (inDepend dp) deps
                   Error _ -> False
          hasDepend _ _ = False
          inDepend :: [(String,String,JSValue)] -> String -> Bool
          inDepend dp pnam = any (\(f,p,_) -> f == fnam && p == pnam) dp

-- | Filter a function description sequence by a list of function identifiers
filterParmods :: Parmods -> [String] -> Parmods
filterParmods parmods funids = filter (reqFilter funids) parmods
    where reqFilter :: [String] -> Parmod -> Bool
          reqFilter rs jso = any (\s -> s == getFunName jso) rs

-- | Filter a function description sequence by a list of function identifier prefixes
prefilterParmods :: Parmods -> [String] -> Parmods
prefilterParmods parmods funids = filter (reqFilter funids) parmods
    where reqFilter :: [String] -> Parmod -> Bool
          reqFilter rs jso = any (\s -> s `isPrefixOf` getFunName jso) rs

-- | Merge two function description sequences.
-- If a function is described in both sequences the description is selected
-- where more parameter descriptions are confirmed. If the same number of descriptions
-- are confirmed always the description in the first sequence is selected.
mergeParmods :: Parmods -> Parmods -> Parmods
mergeParmods parmods parmods2 = M.elems $ M.unionWith confirmedFun (mkmap parmods) (mkmap parmods2)
    where mkmap parmods = M.fromList $ map (\jso -> (getFunName jso,jso)) parmods

confirmedFun :: Parmod -> Parmod -> Parmod
confirmedFun jso jso2 = if uc <= uc2 then jso else jso2
    where uc = length $ filter isRemainingPar $ getFAttrs isParam jso
          uc2 = length $ filter isRemainingPar $ getFAttrs isParam jso2

-- | Sort a function description sequence according to a sequence of function identifiers
-- The result contains all function descriptions where the identifier occurs in the identifier sequence.
-- If an identifier occurs in the sequence more than once, its first occurrence is used.
sortParmods :: Parmods -> [String] -> Parmods
sortParmods parmods funids = catMaybes $ map (insrt parmods) $ nub funids
    where insrt :: Parmods -> String -> Maybe Parmod
          insrt parmods funid = find (\jso -> funid == getFunName jso) parmods

-- | Add parameters from the invocation with the most arguments.
-- For function description with unknown or variadic parameters additional parameter descriptions are added.
addParsFromInvokes :: Parmods -> Parmods
addParsFromInvokes parmods = map addPars parmods
    where invks = map snd $ getInvokes parmods
          invknams = S.toList $ S.fromList $ map getInvokeName invks
          invknums = map (\n -> (n,maximum $ map numArgs $ filter (\o -> getInvokeName o == n) invks)) invknams
          addPars jso = 
              let fnam = getFunName jso
                  nump = getFunNumPars jso
                  invk = find (\(nam,num) -> nam == fnam) invknums
              in if isJust invk && (nump == showJSON "unknown" || nump == showJSON "variadic")
                     then let attrs = fromJSObject jso
                              (bp,r) = break (\(nam,val) -> isDigit $ head nam) attrs
                              (p,ap) = break (\(nam,val) -> not $ isDigit $ head nam) r
                              maxnum = snd $ fromJust invk
                              pnum = length p
                          in if pnum < maxnum
                                then let addpars = zip (map show (iterate (1+) (pnum+1))) $ replicate (maxnum - pnum) $ showJSON "?"
                                     in toJSObject (bp ++ p ++ addpars ++ ap)
                                else jso
                           else jso

numArgs :: JSObject JSValue -> Int
numArgs jso = (length $ fromJSObject jso) - 2

-- | Evaluate a function description sequence by eliminating dependencies.
-- Parameter dependencies are eliminated by following them.
-- The resulting function description contains no dependencies and no invocation lists.
-- Every parameter description has the value "nonlinear", "readonly", "yes", "discarded", or "no".
-- If the input has unconfirmed parameter descriptions or missing required dependencies the 
-- result of the evaluation is undefined.
evaluateParmods :: Parmods -> Parmods
evaluateParmods parmods =
    map (simplifyDescr (evalDependencies (M.unions (map getFunParMap parmods)))) parmods

-- | Internal representation for parameters and parameter descriptions.
-- Parameters are specified as pair (function identifier, parameter identifier).
-- Parameter descriptions are specified as the set of parameters they depend on
-- or as a singleton set containing the pair ("",value) where value is one of
-- "nonlinear", "readonly", "yes", "discarded", "no".
type ParVal = (String,String)
type ParMap = M.Map ParVal (S.Set ParVal)

-- | combine ParMaps
-- If for a parameter occurring in both maps the second set is empty, take the first, otherwise take the second.
-- The second set is empty, if the parameter is described as "depends".
-- Thus, dependencies specified in the invocations are ignored if the parameter description is not "depends".
-- If the parameter is described as "depends" but there is no dependency, it will not be present in the
-- first map and get the set from the second map which is empty. This is detected and handled in simplifyPar.
combineParMap = M.unionsWith combineParameter
    where combineParameter dep desc | null desc = dep
          combineParameter _ desc = desc

-- | Get the parameter map information from a function description.
getFunParMap :: Parmod -> ParMap
getFunParMap jso = combineParMap $ (getParDeps $ getFAttrs isInvokes jso) : (map (getParMap . readValue) $ getFAttrs isParam jso)

readValue :: (String,String,JSValue) -> (String,String,String)
readValue (fnam,pnam,pval) = 
    case readJSON pval of
         Ok a -> (fnam,pnam,a)
         Error msg -> error $ "Cannot read description of " ++ fnam ++ "/" ++ pnam ++ " as string.\n"
                            ++ msg

getParMap :: (String,String,String) -> ParMap
getParMap (fnam,pnam,"depends") = M.singleton (fnam,pnam) S.empty
getParMap (fnam,pnam,val) = M.singleton (fnam,pnam) $ S.singleton ("",val)

getParDeps :: [(String,String,JSValue)] -> ParMap
getParDeps invks =
    if null invks
       then M.empty
       else M.unionsWith S.union $ map getInvkParDeps $ getFunInvokes $ head invks

getInvkParDeps :: (String,JSObject JSValue) -> ParMap
getInvkParDeps (fnam,invk) = M.unionsWith S.union $ map (getInvkSingleParDeps fnam inam) ipars
    where inam = getInvokeName invk
          ipars = filter (\(nam,val) -> (isDigit $ head nam) && isListVal val) $ fromJSObject invk
          isListVal (JSArray _) = True
          isListVal _ = False

getInvkSingleParDeps :: String -> String -> (String, JSValue) -> ParMap
getInvkSingleParDeps fnam inam (ipar, (JSArray fplist)) = 
    M.unions $ map (\(JSString fpar) -> M.singleton (fnam,fromJSString fpar) $ S.singleton (inam,ipar)) fplist

-- | Reduce the parameter map by eliminating all dependencies.
evalDependencies :: ParMap -> ParMap
evalDependencies pm = 
    if M.foldr (\vset b -> b || any (\(f,_) -> not $ null f) vset) False pm 
       then evalDependencies $ M.map (reduceParVals . followDeps pm) pm
       else pm

-- | Replace all parameters in a set by the union of all their ParMap values 
followDeps :: ParMap -> S.Set ParVal -> S.Set ParVal
followDeps pm vs = S.foldr addDeps S.empty vs
    where addDeps pv@("",_) pvs = S.insert pv pvs 
          addDeps pv pvs = if M.notMember pv pm 
                              then error ("missing required invocation: " ++ show pv)
                              else S.union (pm!pv) pvs

reduceParVals :: S.Set ParVal -> S.Set ParVal
reduceParVals vs =
    if any (\(f,v) -> null f && v == "yes") vs
       then S.singleton ("","yes")
       else if all (\(f,_) -> null f) vs && any (\(_,v) -> v == "discarded") vs
                then S.singleton ("","discarded")
                else vs

-- | Simplify a function description by replacing parameter dependencies by the description from the ParMap.
-- Additionally, remove all information about invocations.
simplifyDescr :: ParMap -> Parmod -> Parmod
simplifyDescr pm jso =
    toJSObject $ map (simplifyPar pm fnam) fattrs
    where fattrs = filter (\(anam,_) -> not $ isSuffixOf "invocations" anam) $ fromJSObject jso
          fnam = getFunName jso

simplifyPar :: ParMap -> String -> (String,JSValue) -> (String,JSValue)
simplifyPar pm fnam par@(pnam,(JSString val)) | isDigit $ head pnam =
    if "depends" == fromJSString val 
       then (pnam,showJSON corrVal)
       else par
    where transVal = pm!(fnam,pnam)
          corrVal = if null transVal
                       -- If pm!(fnam,pnam) is empty, it has been described as "depends" but there was no dependency
                       then "no"
                       else snd $ head $ S.toList $ transVal
simplifyPar _ _ attr = attr

-- | Convert a function description sequence to an item property map.
-- The result type is equivalent to ItemProperties, we avoid importing Gencot.Util.Properties here.
convertParmods :: Parmods -> M.Map String [String]
convertParmods parmods = M.unions $ map convertParmod parmods

convertParmod :: Parmod -> M.Map String [String]
convertParmod jso =
    M.unions $ map mkmap $ getFAttrs isParam jso
    where respar = getFunResult jso
          mkmap (fnam,pnam,(JSString js)) = 
              case fromJSString js of
                   "yes" -> M.singleton (mkparnam fnam pnam) [if pnam == respar then "-ar" else "ar"]
                   "no" -> M.singleton (mkparnam fnam pnam) ["ro", "-ar"]
                   "discarded" -> M.singleton (mkparnam fnam pnam) ["-ar"]
                   "readonly" -> M.singleton (mkparnam fnam pnam) ["ro"]
                   _ -> M.empty
          mkparnam fnam pnam =
              fnam ++ "/" ++ (if elem '-' pnam then tail $ snd $ break ('-' ==) pnam else pnam)

