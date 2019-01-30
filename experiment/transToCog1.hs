{-# LANGUAGE PackageImports #-}
module Main where

import "language-c" Language.C as LC hiding (pretty,Pretty)
import Language.C.Data.Ident as LCI
import Language.C.Data.Node as LCN
import Language.C.Data.Position as LCP
import Language.C.Analysis as LCA

import Cogent.Surface as CS
import Cogent.Common.Syntax as CCS
import Cogent.Common.Types as CCT

import Gencot.Input (readFromInput,getDeclEvents)
import Gencot.Origin (Origin,Origin(..),noOrigin,listOrigins,subOrigin,subListOrigins,fstLine,lstLine)
import Gencot.Names (transTagName,transFunName,transToField,mapNameToUpper,mapNameToLower,addInputName)
import Gencot.Cogent.Ast
import Gencot.Cogent.Output (prettyTopLevels)

main :: IO ()
main = do
    globals <- readFromInput
    globals <- addInputName globals
    print $ prettyTopLevels $ transGlobals globals $ getDeclEvents globals constructFilter

constructFilter :: DeclEvent -> Bool
constructFilter (LCA.TagEvent (LCA.EnumDef (LCA.EnumType (LCI.AnonymousRef _) _ _ _))) = False
constructFilter (LCA.DeclEvent (LCA.Declaration _)) = False
constructFilter (LCA.DeclEvent (LCA.ObjectDef _)) = False
constructFilter _ = True

transGlobals :: LCA.GlobalDecls -> [LCA.DeclEvent] -> [GenToplv]
transGlobals g gs = zipWith (transGlobal g) gs $ listOrigins gs

transGlobal :: LCA.GlobalDecls -> LCA.DeclEvent -> Origin -> GenToplv
transGlobal g (LCA.TagEvent (LCA.CompDef (LCA.CompType sueref LCA.StructTag ms _ n))) o = 
    GenToplv o (CS.TypeDec (transTagName g (LCA.TyComp $ LCA.CompTypeRef sueref LCA.StructTag n)) [] 
        (GenType noOrigin (CS.TRecord (transMembers g ms n) (CCT.Boxed False CS.noRepE))))
transGlobal g (LCA.TagEvent (LCA.CompDef (LCA.CompType sueref LCA.UnionTag ms _ n))) o = 
    GenToplv o (CS.AbsTypeDec (transTagName g (LCA.TyComp $ LCA.CompTypeRef sueref LCA.UnionTag n)) [] [])
transGlobal g (LCA.TagEvent (LCA.EnumDef (LCA.EnumType sueref es _ n))) o = 
    GenToplv o (CS.TypeDec (transTagName g (LCA.TyEnum $ LCA.EnumTypeRef sueref n)) [] 
        (GenType noOrigin (CS.TCon "U32" [] markUnbox)))
transGlobal g (LCA.DeclEvent (LCA.FunctionDef (LCA.FunDef (LCA.VarDecl (LCA.VarName idnam _) _ t) s n))) o = 
    GenToplv o (CS.FunDef (transFunName g idnam) (CS.PT [] (transType g t n)) 
        [CS.Alt (transParamNames g ps n) CCS.Regular $ FunBody s])
    where ps = case t of {
        (LCA.FunctionType (LCA.FunType _ ps False) _) -> ps;
        _ -> []
    }
transGlobal g (LCA.DeclEvent (LCA.EnumeratorDef (LCA.Enumerator idnam e _ _))) o =
    GenToplv o (CS.ConstDef (mapNameToLower idnam) 
        (GenType noOrigin (CS.TCon "U32" [] markUnbox)) (ConstExpr e))
transGlobal g (LCA.TypeDefEvent (LCA.TypeDef idnam t _ n)) o = 
    GenToplv o (CS.TypeDec (mapNameToUpper idnam) [] $ transType g t n)
transGlobal _ _ o = GenToplv o (CS.Include "err-unexpected toplevel")

transMembers :: LCA.GlobalDecls -> [LCA.MemberDecl] -> LC.NodeInfo -> [(CCS.FieldName, (GenType, CS.Taken))]
{- TODO: bitfields -}
transMembers g ms n = zipWith (transMember g) ms $ subListOrigins n ms

transMember :: LCA.GlobalDecls -> LCA.MemberDecl -> Origin -> (CCS.FieldName, (GenType, CS.Taken))
transMember g (LCA.MemberDecl (LCA.VarDecl (LCA.VarName (LCI.Ident nam _ _) _) att t) Nothing n) o = 
    (nam, ((GenType o mtype), False))
    where mtype = typeOfGT $ transType g t n
transMember _ _ o = ("fld", ((GenType o CS.TUnit), False))

transParamNames :: LCA.GlobalDecls -> [LCA.ParamDecl] -> LC.NodeInfo -> GenIrrefPatn
transParamNames _ [] _ = GenIrrefPatn noOrigin CS.PUnitel
transParamNames g [pd] n = transParamName g pd $ subOrigin n pd
transParamNames g ps n = 
    GenIrrefPatn noOrigin $ CS.PTuple $ zipWith (transParamName g) ps $ subListOrigins n ps

transParamName :: LCA.GlobalDecls -> LCA.ParamDecl -> Origin -> GenIrrefPatn
transParamName g pd o = 
    GenIrrefPatn o $ CS.PVar (transToField idnam)
    where (LCA.VarDecl (LCA.VarName idnam _) _ _) = getVarDecl pd

transType :: LCA.GlobalDecls -> LCA.Type -> LC.NodeInfo -> GenType 
transType _ (LCA.DirectType TyVoid _ _) _ = 
    GenType noOrigin CS.TUnit
transType g (LCA.DirectType tnam quals _) _ = 
    GenType noOrigin $ CS.TCon (transTNam tnam) [] $ markUnbox
    where transTNam (LCA.TyIntegral TyBool) = "todo-bool"
          transTNam (LCA.TyIntegral TyChar) = "U8"
          transTNam (LCA.TyIntegral TySChar) = "U8"
          transTNam (LCA.TyIntegral TyUChar) = "U8"
          transTNam (LCA.TyIntegral TyShort) = "U16"
          transTNam (LCA.TyIntegral TyUShort) = "U16"
          transTNam (LCA.TyIntegral TyInt) = "U32"
          transTNam (LCA.TyIntegral TyUInt) = "U32"
          transTNam (LCA.TyIntegral TyInt128) = "err-int128"
          transTNam (LCA.TyIntegral TyUInt128) = "err-uint128"
          transTNam (LCA.TyIntegral TyLong) = "U64"
          transTNam (LCA.TyIntegral TyULong) = "U64"
          transTNam (LCA.TyIntegral TyLLong) = "U64"
          transTNam (LCA.TyIntegral TyULLong) = "U64"
          transTNam (LCA.TyFloating _) = "err-float"
          transTNam (LCA.TyComplex _) = "err-complex"
          transTNam (LCA.TyComp _) = transTagName g tnam
          transTNam (LCA.TyEnum (LCA.EnumTypeRef (AnonymousRef _) _)) = "U32"
          transTNam (LCA.TyEnum _) = transTagName g tnam
          transTNam (LCA.TyBuiltin _) = "err-builtin" 
transType g (LCA.PtrType ct@(LCA.DirectType (LCA.TyComp _) cquals _) quals _) n =
    setBoxed $ transType g ct n
transType g (LCA.PtrType at@(LCA.ArrayType t _ aquals _) quals _) n =
    setBoxed $ transType g at n
transType g (LCA.PtrType t quals _) n =
    setBoxed $ prefixType g "P" t n
transType g (LCA.ArrayType t _ quals _) n =
    prefixType g "A" t n
transType _ (LCA.FunctionType (LCA.FunType _ _ True) _) _ = errType "fun-varargs"
transType _ (LCA.FunctionType (LCA.FunTypeIncomplete _ ) _) _ = errType "fun-incompl"
transType g (LCA.FunctionType (LCA.FunType rt ps False) _) n =
    GenType noOrigin $ CS.TFun (transParamTypes g ps n) (transType g rt n)
transType g (LCA.TypeDefType (LCA.TypeDefRef idnam t _) quals _) n =
    GenType noOrigin $ CS.TCon (mapNameToUpper idnam) [] $ markType t

transParamTypes :: LCA.GlobalDecls -> [LCA.ParamDecl] -> LC.NodeInfo -> GenType
transParamTypes _ [] _ = GenType noOrigin CS.TUnit
transParamTypes g [pd] n = transParamType g pd $ subOrigin n pd
transParamTypes g ps n = 
    GenType noOrigin $ CS.TTuple $ zipWith (transParamType g) ps $ subListOrigins n ps

transParamType :: LCA.GlobalDecls -> LCA.ParamDecl -> Origin -> GenType
transParamType g pd o = 
    GenType o $ typeOfGT $ transType g pt $ LC.nodeInfo pd
    where (LCA.VarDecl _ _ pt) = getVarDecl pd

prefixType :: LCA.GlobalDecls -> String -> LCA.Type -> LC.NodeInfo -> GenType
prefixType _ pre (LCA.DirectType TyVoid _ _) n =
    GenType noOrigin $ CS.TCon (pre ++ "_Void") [] markUnbox
prefixType g pre dt@(LCA.DirectType _ _ _) n = 
    GenType noOrigin $ CS.TCon (pre ++ "_" ++ btnam) [] markUnbox
    where (GenType _ (CS.TCon btnam _ _)) = transType g dt n
prefixType g pre (LCA.PtrType t quals _) n = prefixType g (pre ++ "P") t n
prefixType g pre (LCA.ArrayType t _ quals _) n = prefixType g (pre ++ "A") t n
prefixType g pre (LCA.FunctionType (LCA.FunType rt ps False) _) n = prefixType g (pre ++ "F") rt n
prefixType g pre tt@(LCA.TypeDefType _ _ _) n =
    GenType noOrigin $ CS.TCon (pre ++ "_" ++ btnam) [] markUnbox
    where (GenType _ (CS.TCon btnam _ _)) = transType g tt n

setBoxed (GenType o (CS.TCon nam p _)) = (GenType o (CS.TCon nam p markBox))

markType :: LCA.Type -> CCT.Sigil CS.RepExpr
markType (LCA.PtrType t quals _) = markBox
markType (LCA.TypeDefType (LCA.TypeDefRef _ t _) quals _) = markType t
markType _ = markUnbox

markBox = CCT.Boxed False CS.noRepE
markUnbox = CCT.Unboxed

errType :: String -> GenType
errType s = GenType noOrigin $ CS.TCon ("err-" ++ s) [] markUnbox
