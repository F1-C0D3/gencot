{-# LANGUAGE PackageImports #-}
module Gencot.Text.CTypInfo where

import Data.List (intercalate,break,words)
import Data.Map (Map,empty,singleton,unions,union)

import Language.C.Data.Ident as LCI
import Language.C.Data.Node as LCN
import Language.C.Data.Position as LCP
import Language.C.Syntax.AST as LCS
import Language.C.Syntax.Constants as LCC
import qualified Language.C.Analysis as LCA


procStructs :: [LCA.DeclEvent] -> [String]
procStructs decls = map procStruct decls

procStruct :: LCA.DeclEvent -> String
procStruct (LCA.TagEvent (LCA.CompDef (LCA.CompType (LCI.NamedRef (LCI.Ident nam _ _)) LCA.StructTag membs _ _))) =
  nam ++ " " ++ (intercalate " " $ map procMemb membs)
procStruct _ = ""

procMemb :: LCA.MemberDecl -> String 
procMemb (LCA.MemberDecl (LCA.VarDecl (LCA.VarName (LCI.Ident nam _ _) _) _ t) _ _) =
  nam ++ ":" ++ (procType t)
procMemb _ = "error"

procType :: LCA.Type -> String
procType (LCA.TypeDefType (LCA.TypeDefRef (LCI.Ident nam _ _) _ _) _ _) = nam
procType (LCA.PtrType t _ _) = (procType t) ++ "*"
procType (LCA.ArrayType t (LCA.ArraySize _ e) _ _) = (procType t) ++ "[" ++ (procSize e) ++ "]"
procType _ = "error"

procSize :: LCS.CExpr -> String
procSize (LCS.CConst (LCS.CIntConst c _)) = show $ LCC.getCInteger c
procSize _ = "error"

procFuncs :: [LCA.DeclEvent] -> [String]
procFuncs decls = concat $ map procFunc decls

procFunc :: LCA.DeclEvent -> [String]
procFunc (LCA.DeclEvent (LCA.FunctionDef (LCA.FunDef (LCA.VarDecl (LCA.VarName (LCI.Ident nam _ _) _) _ ft) body _))) =
  ((snd $ splitAt 9 nam) ++ " " ++ (procFuntyp ft)) : (procBody body)
procFunc _ = ["error"]

procFuntyp :: LCA.Type -> String
procFuntyp (LCA.FunctionType (LCA.FunType rt (_:(LCA.ParamDecl (LCA.VarDecl _ _ pt) _):[]) _) _) =
  (procType rt) ++ " " ++ (procType pt)
procFuntyp _ = "error"

procBody :: LCS.CStat -> [String]
procBody (LCS.CCompound _ ((LCS.CBlockStmt (LCS.CReturn (Just e) _)):[]) _) = [procCall e]
procBody (LCS.CCompound _ ((LCS.CBlockStmt (LCS.CSwitch _ (LCS.CCompound _ ss _) _)):[]) _) = map procCase ss
procBody _ = ["error"]

procCall :: LCS.CExpr -> String
procCall (LCS.CCall (LCS.CVar (LCI.Ident nam _ _) _) _ _) = nam
procCall _ = "error"

procCase :: LCS.CBlockItem -> String
procCase (LCS.CBlockStmt (LCS.CCase _ (LCS.CReturn (Just e) _) _)) = procCall e
procCase (LCS.CBlockStmt (LCS.CDefault (LCS.CReturn (Just e) _) _)) = procCall e
procCase _ = "error"

-- | Read struct types information.
-- Returns a map from type names to member list with member id and member type
readStructsFromFile :: FilePath -> IO (Map String [(String,String)])
readStructsFromFile file = do 
    inp <- readFile file 
    return $ readStructs $ filter (not . null) $ lines inp

-- | Read function types information.
-- Returns a map from type names to argument and result type and list of functions belonging to the type
readFuntypsFromFile :: FilePath -> IO (Map String (String,String,[String]))
readFuntypsFromFile file = do 
    inp <- readFile file 
    return $ readFuntyps $ filter (not . null) $ lines inp

readStructs :: [String] -> Map String [(String,String)]
readStructs structs = unions (unitType:(map readStruct structs))

unitType = singleton "unit_t" [("dummy","u32")]

readStruct :: String -> Map String [(String,String)]
readStruct struct = singleton (head ws) (map (remcolon . break (== ':')) (tail ws))
    where ws = words struct
          remcolon (a,b) = (a,tail b)

readFuntyps :: [String] -> Map String (String,String,[String])
readFuntyps [] = empty
readFuntyps (fline:rest) = readftyps rest empty fline [] 

readftyps :: [String] -> Map String (String,String,[String]) -> String -> [String] -> Map String (String,String,[String])
readftyps [] m fline funs = union m (singleton ftyp (atyp,rtyp,funs))
    where [ftyp,atyp,rtyp] = words fline
readftyps (l:rest) m fline funs =
    if length ws == 1 then readftyps rest m fline ((head ws):funs)
                      else readftyps rest (readftyps [] m fline (reverse funs)) l []
    where ws = words l
