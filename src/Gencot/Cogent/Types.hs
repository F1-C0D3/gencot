{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Types where

import Data.List (find)

import Language.C.Analysis as LCA

import Cogent.Surface as CS
import Cogent.Common.Syntax as CCS
import Cogent.Common.Types (readonly,bangSigil,Sigil(Unboxed,Boxed),RecursiveParameter(NonRec))

import Gencot.Cogent.Ast -- includes unitType
import Gencot.Origin (noOrigin)
import Gencot.Names (
  mapPtrDeriv, ptrDerivCompName, mapPtrVoid, mapMayNull, variadicTypeName, mapArrDeriv,
  isArrDeriv, arrDerivCompNam, arrDerivHasSize, mapFunDeriv)

-- Construct Types
------------------

genType t = GenType t noOrigin Nothing

-- | Type constructor application.
-- Sigil not used, always boxed so that pretty does not add an unbox marker.
mkConstrType :: CCS.TypeName -> [GenType] -> GenType
mkConstrType n ts = genType (CS.TCon n ts $ Boxed False Nothing)

-- | Type name is a type constructor without arguments.
mkTypeName :: CCS.TypeName -> GenType
mkTypeName s = mkConstrType s []

mkU8Type :: GenType
mkU8Type = mkTypeName "U8"

mkU32Type :: GenType
mkU32Type = mkTypeName "U32"

mkStringType :: GenType
mkStringType = mkTypeName "String"

mkBoolType :: GenType
mkBoolType = mkTypeName "Bool"

mkTupleType :: [GenType] -> GenType
mkTupleType [] = genType CS.TUnit
mkTupleType [t] = t
mkTupleType ts = genType (CS.TTuple ts)

mkCtlType :: GenType
mkCtlType = mkU8Type

mkFunType :: GenType -> GenType -> GenType
mkFunType pt rt = genType (CS.TFun pt rt)

mkRecordType :: [(CCS.FieldName,GenType)] -> GenType
mkRecordType fts = genType (CS.TRecord NonRec (map (\(f,t) -> (f,(t,False))) fts) $ Boxed False Nothing)

-- Array type:
-- depends on mapping of size expression in type name.
-- If size is mapped: builtin array type wrapped in a record with type name added as synonym.
-- Otherwise: abstract type.
-- The first argument is the type name.
-- The second argument is the Cogent size expression.
mkArrayType :: String -> GenExpr -> GenType -> GenType
mkArrayType tnam siz eltyp =
    if arrDerivHasSize tnam
       then addTypeSyn tnam $ mkWrappedArrayType tnam siz eltyp
       else mkConstrType tnam [eltyp]

mkWrappedArrayType :: String -> GenExpr -> GenType -> GenType
mkWrappedArrayType tnam siz eltyp = mkRecordType [(arrDerivCompNam tnam, genType $ CS.TArray eltyp siz Unboxed [])]

-- Pointer type:
-- Wrapper record with cont component and synonym CPtr.
mkPtrType :: GenType -> GenType
mkPtrType tref = addTypeSyn mapPtrDeriv $ mkRecordType [(ptrDerivCompName, tref)]

-- Void Pointer type
mkVoidPtrType :: GenType
mkVoidPtrType = mkTypeName mapPtrVoid

mkTakeType :: Bool -> GenType -> [CCS.FieldName] -> GenType
mkTakeType b (GenType (CS.TBang t) o s) tfs = GenType (CS.TBang (mkTakeType b t tfs)) o s
mkTakeType b (GenType (CS.TUnbox t) o s) tfs = GenType (CS.TUnbox (mkTakeType b t tfs)) o s
mkTakeType b (GenType (CS.TCon cstr [t] sg) o s) tfs | cstr == mapMayNull = GenType (CS.TCon cstr [(mkTakeType b t tfs)] sg) o s
mkTakeType b (GenType (CS.TRecord rp fs s) o _) tfs =
    GenType (CS.TRecord rp fs' s) o Nothing
    where fs' = map (\fld@(fn, (tp, tk)) -> if elem fn tfs then (fn,(tp,b)) else fld) fs

mkArrTakeType :: Bool -> GenType -> [GenExpr] -> GenType
mkArrTakeType b (GenType (CS.TBang t) o s) es = GenType (CS.TBang (mkArrTakeType b t es)) o s
mkArrTakeType b (GenType (CS.TUnbox t) o s) es = GenType (CS.TUnbox (mkArrTakeType b t es)) o s
mkArrTakeType b (GenType (CS.TCon cstr [t] sg) o s) es | cstr == mapMayNull = GenType (CS.TCon cstr [(mkArrTakeType b t es)] sg) o s
mkArrTakeType b (GenType (CS.TRecord rp [(arr,(t,tk))] s) o syn) es = GenType (CS.TRecord rp [(arr,(mkArrTakeType b t es,tk))] s) o syn
mkArrTakeType b (GenType (CS.TArray eltp siz s tels) o _) es =
    GenType (CS.TArray eltp siz s (tels' b)) o Nothing
    where tels' True = (map (\e -> (e,True)) es) ++ tels
          tels' False = filter (\tel -> not $ elem (fst tel) es) tels

mkBangType :: GenType -> GenType
mkBangType t = genType (CS.TBang t)

mkUnboxType :: GenType -> GenType
mkUnboxType t = genType (CS.TUnbox t)

-- Type predicates
------------------

isSizedArrayType :: GenType -> Bool
isSizedArrayType (GenType (CS.TRecord NonRec [(_,((GenType (CS.TArray _ _ _ _) _ _),_))] _) _ (Just syn)) = isArrDeriv syn
isSizedArrayType _ = False

isUnsizedArrayType :: GenType -> Bool
isUnsizedArrayType (GenType (CS.TCon n [_] _) _ _) = isArrDeriv n && not (arrDerivHasSize n)
isUnsizedArrayType _ = False

isArrayType :: GenType -> Bool
isArrayType t = isSizedArrayType t || isUnsizedArrayType t

isUnboxedArrayType :: GenType -> Bool
isUnboxedArrayType (GenType (CS.TBang t) _ _) = isUnboxedArrayType t
isUnboxedArrayType (GenType (CS.TUnbox t) _ _) = isArrayType t
isUnboxedArrayType _ = False

isPtrType :: GenType -> Bool
isPtrType (GenType (CS.TRecord NonRec [(cmpNam,_)] _) _ (Just syn)) = cmpNam == ptrDerivCompName && syn == mapPtrDeriv
isPtrType _ = False

isVoidPtrType :: GenType -> Bool
isVoidPtrType (GenType (CS.TCon cstr [] _) _ _) = cstr == mapPtrVoid
isVoidPtrType _ = False

isStringType :: GenType -> Bool
isStringType (GenType (CS.TCon cstr [] _) _ _) = cstr == "String"
isStringType _ = False

-- Type synonyms
----------------

-- | Add a type synonym for a type.
-- Always attached inside of TBang, TUnbox, and MayNull, so that these modifiers are applied to the synonym.
-- If there is already a synonym, it is overwritten.
addTypeSyn :: CCS.TypeName -> GenType -> GenType
addTypeSyn s (GenType (CS.TBang t) o ms) = GenType (CS.TBang (addTypeSyn s t)) o ms
addTypeSyn s (GenType (CS.TUnbox t) o ms) = GenType (CS.TUnbox (addTypeSyn s t)) o ms
addTypeSyn s (GenType (CS.TCon cstr [t] sg) o ms) | cstr == mapMayNull = GenType (CS.TCon cstr [(addTypeSyn s t)] sg) o ms
addTypeSyn s (GenType t o _) = GenType t o (Just s)

-- | Replace a type using its type synonym, if present.
useTypeSyn :: GenType -> GenType
useTypeSyn (GenType (CS.TBang t) o ms) = GenType (CS.TBang (useTypeSyn t)) o ms
useTypeSyn (GenType (CS.TUnbox t) o ms) = GenType (CS.TUnbox (useTypeSyn t)) o ms
useTypeSyn (GenType (CS.TCon cstr [t] sg) o ms) | cstr == mapMayNull = GenType (CS.TCon cstr [(useTypeSyn t)] sg) o ms
-- array type synonym of form CArr<size> with element type as argument
useTypeSyn (GenType (TRecord _ [(arrx,((GenType (TArray et _ _ _) _ _),_))] _) org (Just syn))
        | isArrDeriv syn && arrDerivCompNam syn == arrx =
    GenType (CS.TCon syn [et] $ Boxed False Nothing) org Nothing
-- pointer type synonym CPtr with referenced type as argument
useTypeSyn (GenType (TRecord _ [(cont,(rt,_))] _) org (Just syn))
        | syn == mapPtrDeriv && ptrDerivCompName == cont =
    GenType (CS.TCon mapPtrDeriv [rt] $ Boxed False Nothing) org Nothing
-- all other type synonyms resulting from typedef or tag names. Without type arguments.
useTypeSyn (GenType _ org (Just syn)) = GenType (CS.TCon syn [] $ Boxed False Nothing) org Nothing
-- type without type synonym
useTypeSyn t@(GenType _ _ Nothing) = t

-- Readonly, Unboxed, and MayNull Types
---------------------------------------

-- Readonly types are always represented by TBang, not in the sigil, so that pretty prints it also for type synonyms.
-- The following normal form is used: whenever TBang affects component types, only the outermost position is marked by TBang.
-- For TTuple always only the components are marked by TBang.
-- Type synonyms are retained because they are wrapped by TBang, with the exception of TTuple.
-- The abstract types CVoidPtr, MayNull, and the pseudo type variadicTypeName are the only abstract types used by
-- Gencot which can be made readonly.
-- After a type has been made readonly, the original type cannot be reconstructed from it.

-- Unboxed types are always represented by TUnbox for the same reason.
-- If TBang and TUnbox or MayNull are combined, TBang is always the outer marker.
-- TUnbox and MayNull cannot be combined, because MayNull is only used to mark linear types.

-- The type constructors TVariant, TRefine, TRPar, TLayout, TTake, TPut, TATake, TAPut are not covered because they are not used by Gencot.

mkReadonly :: GenType -> GenType
mkReadonly t@(GenType (CS.TVar _ _ _) _ _) = mkBangType t
mkReadonly (GenType (CS.TTuple ts) o _) = (GenType (CS.TTuple $ map mkReadonly ts) o Nothing)
mkReadonly (GenType (CS.TRecord rp fs s) o ms) =
    mkBangType (GenType (CS.TRecord rp (map (\(f,(t,tk)) -> (f,(rmRRO t,tk))) fs) s) o ms)
mkReadonly (GenType (CS.TArray t e s ts) o ms) =
    mkBangType (GenType (CS.TArray (rmRRO t) e s ts) o ms)
mkReadonly (GenType (CS.TUnbox t) o ms) =
    mkBangType (GenType (CS.TUnbox $ rmRRO t) o ms)
mkReadonly (GenType (CS.TCon tn ts s) o ms) | (elem tn [mapPtrVoid, mapMayNull, variadicTypeName]) || isArrDeriv tn =
    mkBangType (GenType (CS.TCon tn (map rmRRO ts) s) o ms)
mkReadonly t = t

-- | Remove redundant readonly markers
-- The outermost TBang markers outside of type synonyms are removed, if affected by making the type readonly.
rmRRO :: GenType -> GenType
rmRRO t@(GenType _ _ (Just s)) = t -- stop at type synonym
rmRRO (GenType (CS.TBang t) _ Nothing) = t
rmRRO (GenType (CS.TTuple ts) o Nothing) = (GenType (CS.TTuple (map rmRRO ts)) o Nothing)
rmRRO (GenType (CS.TRecord rp fs s) o Nothing) =
    (GenType (CS.TRecord rp (map (\(f,(t,tk)) -> (f,(rmRRO t,tk))) fs) s) o Nothing)
rmRRO (GenType (CS.TArray t e s ts) o Nothing) =
    (GenType (CS.TArray (rmRRO t) e s ts) o Nothing)
rmRRO (GenType (CS.TUnbox t) o Nothing) =
    (GenType (CS.TUnbox $ rmRRO t) o Nothing)
rmRRO (GenType (CS.TCon tn ts s) o Nothing) | (elem tn [mapPtrVoid, mapMayNull])  =
    (GenType (CS.TCon tn (map rmRRO ts) s) o Nothing)
rmRRO t = t

-- | Remove outermost Bang
unbangType :: GenType -> GenType
unbangType (GenType (CS.TBang t) _ _) = t
unbangType t = t

-- | Readonly or regular
isNonlinear :: GenType -> Bool
isNonlinear (GenType (CS.TBang _) _ _) = True
isNonlinear (GenType (CS.TTuple ts) _ _) = all isNonlinear ts
isNonlinear (GenType (CS.TCon tn _ _) _ _) | (elem tn [mapPtrVoid, mapMayNull, variadicTypeName]) = False
isNonlinear (GenType (CS.TCon tn _ _) _ _) = True
isNonlinear (GenType (CS.TFun _ _) _ _) = True
isNonlinear (GenType CS.TUnit _ _) = True
isNonlinear (GenType (CS.TUnbox t) _ _) = isNonlinearAsUnboxed t
isNonlinear _ = False

isNonlinearAsUnboxed :: GenType -> Bool
isNonlinearAsUnboxed (GenType (CS.TRecord _ fs _) _ _) =
    all (\(_, (t, tkn)) -> tkn || isNonlinear t) fs
isNonlinearAsUnboxed (GenType (CS.TArray t _ _ _) _ _) = isNonlinear t
isNonlinearAsUnboxed _ = True

-- | Escapeable
mayEscape :: GenType -> Bool
mayEscape (GenType (CS.TBang _) _ _) = False
mayEscape (GenType (CS.TTuple ts) _ _) = all mayEscape ts
mayEscape (GenType (CS.TUnbox t) _ _) = mayEscape t
mayEscape (GenType (CS.TRecord _ fs _) _ _) =
    all (\(_, (t, tkn)) -> tkn || mayEscape t) fs
mayEscape (GenType (CS.TArray t _ _ _) _ _) = mayEscape t
mayEscape _ = True

mkUnboxed :: GenType -> GenType
mkUnboxed t@(GenType (CS.TUnbox _) _ _) = t
mkUnboxed (GenType (CS.TBang t) o ms) = (GenType (CS.TBang $ mkUnboxed t) o ms)
mkUnboxed t = mkUnboxType t

isUnboxed :: GenType -> Bool
isUnboxed (GenType (CS.TUnbox _) _ _) = True
isUnboxed (GenType (CS.TBang t) _ _) = isUnboxed t
isUnboxed _ = False

mkMayNull :: GenType -> GenType
mkMayNull t@(GenType (CS.TCon cstr _ _) _ _) | cstr == mapMayNull = t
mkMayNull (GenType (CS.TBang t) o ms) = (GenType (CS.TBang $ mkMayNull t) o ms)
mkMayNull t = mkConstrType mapMayNull [t]

isMayNull :: GenType -> Bool
isMayNull (GenType (CS.TCon cstr _ _) _ _) | cstr == mapMayNull = True
isMayNull (GenType (CS.TBang t) _ _) = isMayNull t
isMayNull _ = False

-- Type selectors for components affected by making the type readonly.
-- Insert TBang marker, if surrounding type is readonly

-- Type of field, unitType if type does not have that field (or any field)
getMemberType :: CCS.FieldName -> GenType -> GenType
getMemberType f (GenType (CS.TRecord _ fs s) _ _) =
    case find (\fld -> fst fld == f) fs of
         Nothing -> unitType
         Just (_,(t,_)) ->
           if isUnboxedArrayType t then getBoxType t else t
getMemberType f (GenType (CS.TBang t) _ _) = mkBangType $ getMemberType f t
-- maynull wrapped type
getMemberType f (GenType (CS.TCon n [t] _) _ _) | n == mapMayNull = getMemberType f t
-- unboxed type
getMemberType f (GenType (CS.TUnbox t) _ _) = getMemberType f t
-- other types -> unitType
getMemberType f _ = unitType

getBoxType :: GenType -> GenType
getBoxType (GenType (CS.TUnbox t) _ _) = t
getBoxType (GenType (CS.TBang t) _ _) = mkBangType $ getBoxType t
getBoxType t = t

getNnlType :: GenType -> GenType
getNnlType (GenType (CS.TCon n [t] _) _ _) | n == mapMayNull = t
getNnlType (GenType (CS.TBang t) _ _) = mkBangType $ getNnlType t
getNnlType t = t

-- Select referenced type for all possible translations of C pointer types.
-- Not applicable to encoded function pointer types.
getDerefType :: GenType -> GenType
-- readonly type
getDerefType (GenType (CS.TBang t) _ _) = mkBangType $ getDerefType t
-- void pointer
getDerefType (GenType (CS.TCon n [] _) _ _) | n == mapPtrVoid = unitType
-- explicit pointer
getDerefType (GenType (CS.TRecord NonRec [(f,(t,_))] _) _ (Just syn)) | f == ptrDerivCompName && syn == mapPtrDeriv = t
-- maynull wrapped type
getDerefType (GenType (CS.TCon n [t] _) _ _) | n == mapMayNull = getDerefType t
-- array types -> element type
getDerefType (GenType (CS.TRecord NonRec [(f,((GenType (CS.TArray t _ _ _) _ _),_))] _) _ (Just syn)) | isArrDeriv syn && f /= ptrDerivCompName =
    if isUnboxedArrayType t then getBoxType t else t
getDerefType (GenType (CS.TCon n [t] _) _ _) | isArrDeriv n && not (arrDerivHasSize n) =
    if isUnboxedArrayType t then getBoxType t else t
-- other types -> make unboxed
getDerefType t = mkUnboxed t

-- | Type selectors for other components

getResultType :: GenType -> GenType
getResultType (GenType (CS.TFun _ rt) _ _) = rt

getParamType :: GenType -> GenType
getParamType (GenType (CS.TFun pt _) _ _) = pt

getLeadType :: GenType -> GenType
getLeadType (GenType (CS.TTuple (t : ts)) _ _) = t
getLeadType t = t

-- | Transfer property effects

-- | Transfer effects of Read-Only, Not-Null, and No-String from first argument to second.
transferProperties :: GenType -> GenType -> GenType
transferProperties (GenType (CS.TBang t) _ _) t2 = mkReadonly $ transferProperties t t2
transferProperties t1 t2 | isStringType t2 && (not $ isStringType t1) = t1
transferProperties t1 t2 | isMayNull t2 && (not $ isMayNull t1) = getNnlType t2
transferProperties _ t = t
