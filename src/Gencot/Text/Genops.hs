{-# LANGUAGE PackageImports #-}
module Gencot.Text.Genops where

import Data.Map (Map,(!?))
import Data.List (transpose,isPrefixOf)
import Data.Maybe (isNothing,isJust,fromJust,catMaybes)
import qualified Data.Text as T

procGenops :: (Map String [(String,String)]) -> (Map String (String,String,[String])) -> String -> String
procGenops structs funtyps inp = T.unpack $ insertDefs (genInitClear structs funtyps ts) exp
    where (ts,fs) = parseTemplates $ T.pack inp
          pts = map (T.pack . (processTemplate structs funtyps)) ts
          exp = T.concat $ concat $ transpose [fs,pts]

-- | Internal representation of a template.
-- Template name, list of types, list of expressions.
-- The template 
--   genopsTemplate("MyTemp", (typ1) expr1, "genopsNext", (typ2) expr2, "genopsEnd")
-- becomes
--   ("MyTemp", ["typ1","typ2"], ["expr1","expr2"])
type Template = (String, [String], [String])

startTmpl = T.pack "genopsTemplate"
endTmpl = T.pack "\"genopsEnd\""
sepTmpl = T.pack "\"genopsNext\""

-- | Retrieve all templates from a string.
-- Returns the list of templates and the list of remaining string fragments.
parseTemplates :: T.Text -> ([Template],[T.Text])
parseTemplates inp = (map (readTemplate . T.tail . T.stripStart . head) h2, 
                      (head h1):(map (T.tail . T.stripStart . head . tail) h2))
    where h1 = T.splitOn startTmpl inp        -- [pref, "(\"nam\",...,\"genopsEnd\")...", ...]
          h2 = map (T.splitOn endTmpl) (tail h1)   -- [ ["(\"nam\",...," ,")..."], ...]

-- | Read template from a string.
-- Input has the form: "name", (typ1) expr1, "genopsNext", ..., "genopsNext", (typn) exprn,
readTemplate :: T.Text -> Template
readTemplate inp = (T.unpack nam, map (T.unpack . T.concat . T.words) ts, map (T.unpack . T.strip . T.tail) es)
    where 
        (nam,rest1) = T.break (== '"') (T.tail (T.strip inp))  -- rest1: ", (typ1) expr1, ...
        args1 = T.splitOn sepTmpl (T.tail rest1) -- [ ... ", (typi) expri," ... ]
        (ts,es) = unzip $ map ((T.break (== ')')) . T.tail . T.strip . (T.dropAround (== ',')) . T.strip) args1 -- [ ... ("typi","expri") ... ]

-- | Process a template and return its expansion as a string.
processTemplate :: (Map String [(String,String)]) -> (Map String (String,String,[String])) -> Template -> String
processTemplate structs _ (nam,[typ],_) | nam == "DefaultVal" = processDefaultVal nam structs typ
processTemplate structs _ (nam,[typ],[expr]) | nam == "InitStruct" = processInitStruct nam structs typ expr
processTemplate structs _ (nam,[typ],[expr]) | nam == "ClearStruct" = processClearStruct nam structs typ expr
processTemplate structs _ (nam,[typ],[expr]) | nam == "ArrayPointer" = processArrayPointer nam structs typ expr
processTemplate structs _ (nam,[typ],[expr]) | nam == "ArraySize" = processArraySize nam structs typ expr
processTemplate _ _ (nam,_,_) = errTmpl nam "unknown template name"

errTmpl nam mess = concat ["genopsTemplateError(",nam,":",mess,")"]

processDefaultVal :: String -> (Map String [(String,String)]) -> String -> String
processDefaultVal nam structs typ =
    if isNothing errpnts
       then res
       else errTmpl nam (fromJust errpnts)
    where (err,pnts,res) = getDefaultVal structs typ
          epnts = ("contains pointer types: "++(show pnts))
          errpnts = 
              if isNothing err
                 then 
                   if null pnts then Nothing else Just epnts
                 else 
                   if null pnts then err else Just ((fromJust err)++" and "++epnts) 

getDefaultVal :: (Map String [(String,String)]) -> String -> (Maybe String, [String], String)
getDefaultVal _ "u8" = (Nothing, [], "0")
getDefaultVal _ "u16" = (Nothing, [], "0")
getDefaultVal _ "u32" = (Nothing, [], "0")
getDefaultVal _ "u64" = (Nothing, [], "0")
getDefaultVal _ "tag_t" = (Nothing, [], "")  -- dummy so that we can map getDefaultVal to variant type translations
getDefaultVal _ "char*" = (Nothing, [], "\"\"")
getDefaultVal _ typ | "CFunPtr_" `isPrefixOf` typ = (Nothing, [], "(void*)0")
getDefaultVal _ typ | last typ == '*' = (Nothing, [typ], "")
getDefaultVal structs typ | elem '[' typ =
    if isNothing err && null pnt 
       then (Nothing, [], "{ "++elres++" }")
       else (err,pnt,"")
    where (eltyp,_) = break (== '[') typ
          (err,pnt,elres) = getDefaultVal structs eltyp
getDefaultVal structs typ =
    if isNothing tt 
       then (Just ("unknown struct type "++typ), [], "")
       else let ttl = fromJust tt
                (err,pnt,ress) = joinerr $ map ((getDefaultVal structs) . snd) ttl
            in if isNothing err && null pnt
                  then if "tag_t" == (snd $ head ttl)
                       then variantDefault (head $ tail ress) (head $ tail ttl) typ
                       else recordDefault (head ress) (head ttl) typ
                  else (err,pnt,"")
    where tt = structs !? typ
          joinerr ttl = 
              let (errs,pnts,ress) = unzip3 ttl
                  errs' = catMaybes errs
                  err = if null errs' then Nothing else Just $ head errs'
              in (err, concat pnts, ress)
          variantDefault v m t = (Nothing, [], "("++typ++"){ .tag = TAG_ENUM_"++(fst m)++", "++(fst m)++"= "++v++" }")
          recordDefault v m t =  (Nothing, [], "("++typ++"){ ."++(fst m)++"= "++v++" }")

processInitStruct :: String -> (Map String [(String,String)]) -> String -> String -> String
processInitStruct nam structs typ expr = ""

processClearStruct :: String -> (Map String [(String,String)]) -> String -> String -> String
processClearStruct nam structs typ expr = ""

processArrayPointer :: String -> (Map String [(String,String)]) -> String -> String -> String
processArrayPointer nam structs typ expr =
    if isJust err
       then errTmpl nam (fromJust err)
       else if mid == "" 
               then concat ["&(",expr,").p1->arr"]  -- explicitly sized array
               else concat ["(",expr,")",acc,mid,".data"]  -- C array
    where (err,mid,_) = getArrayType typ structs
          acc = if last typ == '*' then "->" else "."

processArraySize :: String -> (Map String [(String,String)]) -> String -> String -> String
processArraySize nam structs typ expr =
    if isJust err
       then errTmpl nam (fromJust err)
       else if res == ""
               then concat ["(",expr,").p2"]  -- explicitly sized array
               else res  -- C array
    where (err,res) = getArraySize typ structs

getArrayType :: String -> (Map String [(String,String)]) -> (Maybe String,String,String)
getArrayType typ structs =
    if isNothing tt 
       then (Just ("unknown struct type "++t),"","")
       else let ttl = fromJust tt
            in if length ttl == 1
                  then (Nothing, fst $ head ttl, snd $ head ttl)
                  else if length ttl /= 2
                          then (Just ("type "++t++" must have atmost two members"),"","")
                          else let p1 = fst $ head ttl
                                   p2 = fst $ head $ tail ttl
                                   u64 = snd $ head $ tail ttl
                               in if p1 == "p1" && p2 == "p2" && u64 == "u64" && s == ""
                                     then (Nothing, "", "")
                                     else (Just ("no explicitly sized array type: " ++typ),"","")
    where (t,s) = break (== '*') typ
          tt = structs !? t

getArraySize :: String -> (Map String [(String,String)]) -> (Maybe String,String)
getArraySize typ structs =
    if isJust err
       then (err,"")
       else if mtp == ""
               then (Nothing, "")
               else let tt = structs !? mtp
                    in if isNothing tt
                          then (Just ("unknown struct type "++mtp),"")
                          else let ttl = fromJust tt
                               in if length ttl /= 1
                                     then (Just ("type "++mtp++" must have only one member"),"")
                                     else let (mmid,mmtp) = head ttl
                                          in if mmid /= "data"
                                                then (Just ("member of type "++mtp++" must be named \"data\""),"")
                                                else getSize mmtp
    where (err,_,mtp) = getArrayType typ structs
          getSize mmtp = 
              let (_,h) = break (== '[') mmtp
              in if null h 
                    then (Just ("type "++mmtp++" of data member is no array type"),"")
                    else (Nothing, init $ tail h)

genInitClear :: (Map String [(String,String)]) -> (Map String (String,String,[String])) -> [Template] -> T.Text
genInitClear structs funtyps ts = T.pack ""

defsMarker = T.pack "int genopsInitClearDefinitions;"

insertDefs :: T.Text -> T.Text -> T.Text
insertDefs defs text = T.replace defsMarker defs text 
