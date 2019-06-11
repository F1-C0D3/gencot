{-# LANGUAGE PackageImports, TypeSynonymInstances, FlexibleInstances #-}

-- | Read and process JSON function descriptions.
-- A function description is represented as a JSON object and describes a function or a function pointer. 
-- It mainly consists of a description of the function parameters. 
-- For a function definition, it additionally describes all invocations of functions
-- in the function body.
module Gencot.Json.Process where

import qualified Data.Set as S (toList,fromList,difference)
import Data.List (find)
import Data.Maybe (mapMaybe,isJust,fromJust)
import Data.Char (isDigit)
import Text.JSON

qmark = showJSON "?"
jsEmpty = JSArray []

-- | Read a sequence of function descriptions from stdin.
readParmods :: FilePath -> IO [JSObject JSValue]
readParmods file = do 
    inp <- readFile file 
    case decode inp of
         Ok res -> return res
         Error msg -> error msg

showRemainingPars :: [JSObject JSValue] -> [String]
showRemainingPars parmods =
    map showPar $ getFunAttrs isRemainingPar parmods
    where showPar (fun,par,mod) = "  " ++ fun ++ "/" ++ par

-- | From a function description sequence retrieve all function attributes satisfying a predicate.
-- The predicate is applied to all attributes of all function descriptions.
-- The resulting list contains triples of function name, attribute name and attribute value
getFunAttrs :: ((String,String,JSValue) -> Bool) -> [JSObject JSValue] -> [(String,String,JSValue)]
getFunAttrs pred parmods = concatMap (getFAttrs pred) parmods

getFAttrs :: ((String,String,JSValue) -> Bool) -> JSObject JSValue -> [(String,String,JSValue)]
getFAttrs pred jso = mapMaybe (selAttr pred) $ attrs
    where attrs = map (\(nam,val) -> (fnam,nam,val)) $ fromJSObject jso
          fnam = getFunName jso

getFunName :: JSObject JSValue -> String
getFunName jso = case valFromObj "f_name" jso of
                      Ok s -> s
                      Error msg -> error $ "Name not found in function description:\n" ++ encode jso ++ "\n" ++ msg

getFunNumPars :: JSObject JSValue -> JSValue
getFunNumPars jso = case valFromObj "f_num_params" jso of
                      Ok s -> s
                      Error msg -> error $ "Number of parameters not found in function description:\n" ++ encode jso ++ "\n" ++ msg

selAttr :: ((String,String,JSValue) -> Bool) -> (String,String,JSValue) -> Maybe (String,String,JSValue)
selAttr pred attr = if pred attr then Just attr else Nothing

isRemainingPar :: (String,String,JSValue) -> Bool
isRemainingPar (_,nam,val) | isDigit $ head nam =
    case val of
         JSString jstr -> '?' == (head $ fromJSString jstr)
         _ -> False
isRemainingPar _ = False

showRequired  :: [JSObject JSValue] -> [String]
showRequired parmods =
    map showReq $ getRequired parmods
    where showReq req = "  " ++ req

-- | Get the required invocations from a function description sequence.
-- This are all invocations on which a parameter depends which is specified as dependent, 
-- where the invocation is not described in the sequence.
-- The result is the list of the names of all such invocations, without duplicates.
getRequired :: [JSObject JSValue] -> [String]
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
getInvokes :: [JSObject JSValue] -> [(String,JSObject JSValue)]
getInvokes parmods = concatMap getFunInvokes $ getFunAttrs isInvokes parmods
    where getFunInvokes :: (String,String,JSValue) -> [(String,JSObject JSValue)]
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
        
-- | Add the invocations required by a function description sequence from another function description sequence
addRequired :: [JSObject JSValue] -> [JSObject JSValue] -> [JSObject JSValue]
addRequired inparmods addparmods =
    inparmods ++ filter (reqFilter (getRequired inparmods)) addparmods
    where reqFilter :: [String] -> JSObject JSValue -> Bool
          reqFilter rs jso = any (\s -> s == getFunName jso) rs

-- | Add parameters from the invcation with the most arguments.
-- For function description with unknown or variadic parameters additional parameter descriptions are added.
addParsFromInvokes :: [JSObject JSValue] -> [JSObject JSValue]
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
