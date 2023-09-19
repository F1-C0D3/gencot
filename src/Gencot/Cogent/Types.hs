{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Types where

import Data.List (find, isPrefixOf)
import Data.Maybe (Maybe)

import Language.C.Analysis as LCA

import Cogent.Surface as CS
import Cogent.Common.Syntax as CCS
import Cogent.Common.Types (readonly,unboxed,bangSigil,Sigil(Unboxed,Boxed),RecursiveParameter(NonRec))

import Gencot.Cogent.Ast -- includes unitType
import Gencot.Origin (noOrigin)
import Gencot.Names (
  mapPtrDeriv, ptrDerivCompName, mapPtrVoid, mapMayNull, variadicTypeName, mapArrDeriv,
  isArrDeriv, isArrDerivComp, arrDerivCompNam, arrDerivHasSize, mapFunDeriv)

-- Types used by Gencot in the Cogent AST
-----------------------------------------

-- Only the following type variants are used and covered in the functions in this module:
-- TCon: Basic types, function pointer, Gencot abstract types.
--   Using sigil for readonly/unboxed.
-- TRecord: struct types, wrappers for arrays and pointers.
--   Using sigil for readonly/unboxed. Using take list for take/put.
-- TArray: array types, always unboxed and wrapped in TRecord.
--   Using take list for take/put.
-- TFun: function types.
-- TTuple: function parameters, function results, parallel bindings.
-- TUnit: void type.

-- Sigils
---------

-- In the Gencot Cogent AST the optional layout in the boxed sigil is never used and replaced by ().
type GCSigil = Sigil (Maybe ())

noSigil = Boxed False Nothing

roSigil = Boxed True Nothing

ubSigil = Unboxed

-- Construct Types
------------------

genType t = GenType t noOrigin Nothing

-- | Type constructor application.
-- Sigil not used, always boxed so that pretty does not add an unbox marker.
mkConstrType :: CCS.TypeName -> [GenType] -> GCSigil -> GenType
mkConstrType n ts sg = genType (CS.TCon n ts sg)

-- | Type name is a type constructor without arguments.
mkTypeName :: CCS.TypeName -> GenType
mkTypeName s = mkConstrType s [] noSigil

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
mkRecordType fts = genType (CS.TRecord NonRec (map (\(f,t) -> (f,(t,False))) fts) noSigil)

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
       else mkConstrType tnam [eltyp] noSigil

mkWrappedArrayType :: String -> GenExpr -> GenType -> GenType
mkWrappedArrayType tnam siz eltyp = mkRecordType [(arrDerivCompNam tnam, genType $ CS.TArray eltyp siz ubSigil [])]

-- Pointer type:
-- Wrapper record with cont component and synonym CPtr.
mkPtrType :: GenType -> GenType
mkPtrType tref = addTypeSyn mapPtrDeriv $ mkRecordType [(ptrDerivCompName, tref)]

-- Void Pointer type
mkVoidPtrType :: GenType
mkVoidPtrType = mkTypeName mapPtrVoid

mkTakeType :: Bool -> GenType -> [CCS.FieldName] -> GenType
mkTakeType b (GenType (CS.TCon cstr [t] sg) o s) tfs | cstr == mapMayNull = GenType (CS.TCon cstr [(mkTakeType b t tfs)] sg) o s
mkTakeType b (GenType (CS.TRecord rp fs s) o _) tfs =
    GenType (CS.TRecord rp fs' s) o Nothing
    where fs' = map (\fld@(fn, (tp, tk)) -> if elem fn tfs then (fn,(tp,b)) else fld) fs

mkArrTakeType :: Bool -> GenType -> [GenExpr] -> GenType
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

-- Type synonyms
----------------

-- Used for: typedef names, struct tags, array alias with size (CArr<size>), pointer alias (CPtr).
-- Type synonyms are represented by attaching the synonym name to the aliased type.
-- Array and pointer aliases have a single type argument which is determined as part of the aliased type.
-- All other type synonyms have no type arguent.
-- From the C program, type synonyms can only be attached to TCon, TRecord, TFun, and TUnit.

-- | Add a type synonym for a type.
-- If the type has a sigil, it is copied to the synonym.
-- If there is already a synonym, it is overwritten, preserving its sigil.
-- For a MayNull type the synonym is always attached to the argument type.
addTypeSyn :: CCS.TypeName -> GenType -> GenType
addTypeSyn s (GenType (CS.TCon cstr [a] sg) o ms) | cstr == mapMayNull = GenType (CS.TCon cstr [(addTypeSyn s a)] sg) o ms
addTypeSyn s (GenType t o _) = GenType t o $ Just s

-- | Replace a type using its type synonym, if present.
-- Transfer an existing sigil from the type to the synonym.
-- Synonyms with a type argument (CArr<size> and CPtr) are treated specifically to transfer the argument
useTypeSyn :: GenType -> GenType
useTypeSyn (GenType (CS.TCon cstr [a] sg) o ms) | cstr == mapMayNull = GenType (CS.TCon cstr [(useTypeSyn a)] sg) o ms
-- array type synonym of form CArr<size> with element type as argument
useTypeSyn (GenType (CS.TRecord _ [(arrx,((GenType (CS.TArray et _ _ _) _ _),_))] sg) org (Just syn))
        | isArrDeriv syn && arrDerivCompNam syn == arrx =
    GenType (CS.TCon syn [et] sg) org Nothing
-- pointer type synonym CPtr with referenced type as argument
useTypeSyn (GenType (CS.TRecord _ [(cont,(rt,_))] sg) org (Just syn))
        | syn == mapPtrDeriv && ptrDerivCompName == cont =
    GenType (CS.TCon syn [rt] sg) org Nothing
-- all other type synonyms resulting from typedef or tag names. Without type arguments.
useTypeSyn (GenType (CS.TCon _ _ sg) org (Just syn)) = GenType (CS.TCon syn [] sg) org Nothing
useTypeSyn (GenType (CS.TRecord _ _ sg) org (Just syn)) = GenType (CS.TCon syn [] sg) org Nothing
useTypeSyn (GenType (CS.TArray _ _ sg _) org (Just syn)) = GenType (CS.TCon syn [] sg) org Nothing
useTypeSyn (GenType (CS.TFun _ _) org (Just syn)) = GenType (CS.TCon syn [] noSigil) org Nothing
useTypeSyn (GenType (CS.TUnit) org (Just syn)) = GenType (CS.TCon syn [] noSigil) org Nothing
-- type without type synonym
useTypeSyn t@(GenType _ _ Nothing) = t

-- Readonly, Unboxed, and MayNull Types
---------------------------------------

-- Readonly types are represented in normal form. The bang marker is placed as deep as possible, i.e. at all TRecord,
-- TArray, and TCon which are affected. All deeper bang markers are redundant and are removed.
-- The only affected TCon are CVoidPtr, CArrXX, variadicTypeName, and MayNull (see below).
-- This makes it possible to always represent the bang marker in the sigil without using TBang.
-- After a type has been made readonly, the original type cannot be reconstructed from it.
-- Attached type synonyms always use the sigil of the main type. If a synonym is attached to an unboxed
-- TRecord/TArray/TCon, no bang marker is used for the synonym, even if the corresponding typedef name has been declared
-- readonly by an item property.

-- Unboxed types are also represented using the sigil without using TUnbox, and using it also for attached type synonyms.
-- Thus a type or type synonym can never be marked readonly and unboxed at the same time.

-- MayNull types are represented by a TCon with a single type argument. The type argument is always either a boxed TRecord
-- or the boxed TCon for CVoidPtr or CArrXX. The sigil of the type argument is always repeated in the MayNull TCon so
-- that it is printed in the generated code, for processing it is ignored.

-- | Make readonly.
-- Unchanged if already readonly.
mkReadonly :: GenType -> GenType
mkReadonly (GenType (CS.TTuple ts) o ms) = (GenType (CS.TTuple $ map mkReadonly ts) o ms)
mkReadonly (GenType (CS.TRecord rp fs (Boxed False _)) o ms) =
    GenType (CS.TRecord rp (map (\(f,(t,tk)) -> (f,(rmRRO t,tk))) fs) roSigil) o ms
mkReadonly (GenType (CS.TRecord rp fs Unboxed) o ms) =
    GenType (CS.TRecord rp (map (\(f,(t,tk)) -> (f,(mkReadonly t,tk))) fs) ubSigil) o ms
mkReadonly (GenType (CS.TArray t e Unboxed ts) o ms) = GenType (CS.TArray (mkReadonly t) e ubSigil ts) o ms
mkReadonly (GenType (CS.TCon tn ts (Boxed False _)) o ms) | (elem tn [mapPtrVoid, mapMayNull, variadicTypeName, "Option"]) || isArrDeriv tn =
    GenType (CS.TCon tn (map mkReadonly ts) roSigil) o ms
mkReadonly t = t

-- | Remove redundant readonly markers
rmRRO :: GenType -> GenType
rmRRO (GenType (CS.TTuple ts) o ms) = GenType (CS.TTuple (map rmRRO ts)) o ms
rmRRO (GenType (CS.TRecord rp fs (Boxed _ _)) o ms) =
    (GenType (CS.TRecord rp (map (\(f,(t,tk)) -> (f,(rmRRO t,tk))) fs) noSigil) o ms)
rmRRO (GenType (CS.TArray t e Unboxed ts) o ms) = GenType (CS.TArray (rmRRO t) e ubSigil ts) o ms
rmRRO (GenType (CS.TCon tn ts (Boxed _ _)) o ms) = GenType (CS.TCon tn (map rmRRO ts) noSigil) o ms
rmRRO t = t

-- | Remove outermost Bang marker
-- (Should not be needed).
unbangType :: GenType -> GenType
unbangType (GenType (CS.TRecord rp fs (Boxed _ _)) o ms) = GenType (CS.TRecord rp fs noSigil) o ms
unbangType (GenType (CS.TCon tn ts (Boxed _ _)) o ms) = GenType (CS.TCon tn ts noSigil) o ms
unbangType t = t

mkUnboxed :: GenType -> GenType
mkUnboxed t@(GenType (CS.TCon tn _ _) _ _) | tn == mapMayNull = t
mkUnboxed (GenType (CS.TCon tn ts (Boxed _ _)) o ms) = GenType (CS.TCon tn ts ubSigil) o ms
mkUnboxed (GenType (CS.TRecord rp fs (Boxed _ _)) o ms) = GenType (CS.TRecord rp fs ubSigil) o ms
mkUnboxed t = t

mkMayNull :: GenType -> GenType
mkMayNull t@(GenType (CS.TCon tn _ _) _ _) | tn == mapMayNull = t
mkMayNull t@(GenType (CS.TCon _ _ sg) _ _) = mkConstrType mapMayNull [t] sg
mkMayNull t@(GenType (CS.TRecord _ _ sg) _ _) = mkConstrType mapMayNull [t] sg
mkMayNull t = mkConstrType mapMayNull [t] noSigil

mkOption :: GenType -> GenType
mkOption t = mkConstrType "Option" [t] noSigil

-- Type predicates
------------------

isSizedArrayType :: GenType -> Bool
isSizedArrayType (GenType (CS.TRecord NonRec [(f,((GenType (CS.TArray _ _ _ _) _ _),_))] _) _ (Just _)) =
    isArrDerivComp f
isSizedArrayType _ = False

isUnsizedArrayType :: GenType -> Bool
isUnsizedArrayType (GenType (CS.TCon n [_] _) _ _) = isArrDeriv n && not (arrDerivHasSize n)
isUnsizedArrayType _ = False

isArrayType :: GenType -> Bool
isArrayType t = isSizedArrayType t || isUnsizedArrayType t

isUnboxedArrayType :: GenType -> Bool
isUnboxedArrayType t = isArrayType t && isUnboxed t

isPtrType :: GenType -> Bool
isPtrType (GenType (CS.TRecord NonRec [(cmpNam,_)] _) _ (Just _)) =
    cmpNam == ptrDerivCompName -- may have arbitrary type synonym!
isPtrType _ = False

isVoidPtrType :: GenType -> Bool
isVoidPtrType (GenType (CS.TCon cstr [t] _) _ _) | cstr == mapMayNull = isVoidPtrType t
isVoidPtrType (GenType (CS.TCon cstr [] _) _ _) = cstr == mapPtrVoid
isVoidPtrType _ = False

isStringType :: GenType -> Bool
isStringType (GenType (CS.TCon cstr [] _) _ _) = cstr == "String"
isStringType _ = False

isBoolType :: GenType -> Bool
isBoolType (GenType (CS.TCon cstr [] _) _ _) = cstr == "Bool"
isBoolType _ = False

isTupleType :: GenType -> Bool
isTupleType (GenType (CS.TTuple _) _ _) = True
isTupleType _ = False

isUnitType :: GenType -> Bool
isUnitType (GenType CS.TUnit _ _) = True
isUnitType _ = False

-- | Readonly or regular
isNonlinear :: GenType -> Bool
isNonlinear (GenType (CS.TTuple ts) _ _) = all isNonlinear ts
isNonlinear (GenType (CS.TCon tn [t] _) _ _) | tn == mapMayNull = isNonlinear t
isNonlinear (GenType (CS.TCon tn _ sg) _ _) | (elem tn [mapPtrVoid, variadicTypeName]) || isArrDeriv tn = readonly sg || unboxed sg
isNonlinear (GenType (CS.TCon _ _ _) _ _) = True
isNonlinear (GenType (CS.TRecord _ fs sg) _ _) = readonly sg || (unboxed sg && all (\(_,(t,tkn)) -> tkn || isNonlinear t) fs)
isNonlinear (GenType (CS.TArray t _ Unboxed _) _ _) = isNonlinear t
isNonlinear _ = True

isNonlinearAsUnboxed :: GenType -> Bool
isNonlinearAsUnboxed (GenType (CS.TRecord _ fs _) _ _) = all (\(_, (t, tkn)) -> tkn || isNonlinear t) fs
isNonlinearAsUnboxed (GenType (CS.TArray t _ _ _) _ _) = isNonlinear t
isNonlinearAsUnboxed (GenType (CS.TCon tn [t] _) _ _) | tn == mapMayNull = isNonlinear t
isNonlinearAsUnboxed _ = True

isRegular :: GenType -> Bool
isRegular (GenType (CS.TTuple ts) _ _) = all isRegular ts
isRegular (GenType (CS.TCon tn _ _) _ _) | (elem tn [mapPtrVoid, mapMayNull, variadicTypeName]) || isArrDeriv tn = False
isRegular (GenType (CS.TCon _ _ _) _ _) = True
isRegular (GenType (CS.TRecord _ fs sg) _ _) = unboxed sg && all (\(_,(t,tkn)) -> tkn || isRegular t) fs
isRegular (GenType (CS.TArray t _ Unboxed _) _ _) = isRegular t
isRegular _ = True

-- | Escapeable
mayEscape :: GenType -> Bool
mayEscape (GenType (CS.TTuple ts) _ _) = all mayEscape ts
mayEscape (GenType (CS.TRecord _ fs sg) _ _) =
    (not $ readonly sg) && all (\(_, (t, tkn)) -> tkn || mayEscape t) fs
mayEscape (GenType (CS.TArray t _ Unboxed _) _ _) = mayEscape t
mayEscape (GenType (CS.TCon tn [t] _) _ _) | tn == mapMayNull = mayEscape t
mayEscape (GenType (CS.TCon _ _ sg) _ _) = not $ readonly sg
mayEscape _ = True

isReadonly :: GenType -> Bool
isReadonly (GenType (CS.TCon _ _ sg) _ _) = readonly sg
isReadonly (GenType (CS.TRecord _ _ sg) _ _) = readonly sg
isReadonly (GenType (CS.TArray _ _ Unboxed _) _ _) = False
isReadonly _ = False

isUnboxed :: GenType -> Bool
isUnboxed (GenType (CS.TCon _ _ sg) _ _) = unboxed sg
isUnboxed (GenType (CS.TRecord _ _ sg) _ _) = unboxed sg
isUnboxed (GenType (CS.TArray _ _ Unboxed _) _ _) = True
isUnboxed _ = False

isMayNull :: GenType -> Bool
isMayNull (GenType (CS.TCon cstr _ _) _ _) | cstr == mapMayNull = True
isMayNull _ = False

isArithmetic :: GenType -> Bool
isArithmetic (GenType (CS.TCon tn [] _) _ _) | (elem tn ["U8", "U16", "U32", "U64"]) = True
isArithmetic _ = False

-- | Readonly compatible
-- Assumes that types differ atmost by MayNull or read-only
-- or one is String and the other is pointer to U8
-- or one is CVoidPtr and the other is some pointer.
roCmpTypes :: GenType -> GenType -> Bool
roCmpTypes (GenType CS.TUnit _ _) (GenType CS.TUnit _ _) = True
roCmpTypes (GenType (CS.TFun _ _) _ _) (GenType (CS.TFun _ _) _ _) = True
roCmpTypes (GenType (CS.TTuple ts1) _ _) (GenType (CS.TTuple ts2) _ _) =
    and $ map (uncurry roCmpTypes) $ zip ts1 ts2
roCmpTypes (GenType (CS.TCon tn1 [t1] _) _ _) t2 | tn1 == mapMayNull = roCmpTypes t1 t2
roCmpTypes t1 (GenType (CS.TCon tn2 [t2] _) _ _) | tn2 == mapMayNull = roCmpTypes t1 t2
roCmpTypes (GenType (CS.TCon tn1 _ _) _ _) (GenType (CS.TCon tn2 _ _) _ _) | tn1 == "String" && tn2 == "String" = True
roCmpTypes (GenType (CS.TCon tn1 _ _) _ _) t2 | tn1 == "String" = isReadonly t2
roCmpTypes t1 (GenType (CS.TCon tn2 _ _) _ _) | tn2 == "String" = isReadonly t1
roCmpTypes (GenType (CS.TCon _ _ sg1) _ _) (GenType (CS.TCon _ _ sg2) _ _) = sg1 == sg2
roCmpTypes (GenType (CS.TCon tn1 _ sg1) _ _) (GenType (CS.TRecord _ _ sg2) _ _) | tn1 == mapPtrVoid = sg1 == sg2
roCmpTypes (GenType (CS.TRecord _ _ sg1) _ _) (GenType (CS.TCon tn2 _ sg2) _ _) | tn2 == mapPtrVoid = sg1 == sg2
roCmpTypes (GenType (CS.TRecord _ _ (Boxed True _)) _ _) (GenType (CS.TRecord _ _ (Boxed True _)) _ _) = True
roCmpTypes (GenType (CS.TRecord _ fs1 sg1) _ _) (GenType (CS.TRecord _ fs2 sg2) _ _) =
    sg1 == sg2 && (and $ map (\((_,(t1,_)),(_,(t2,_))) -> roCmpTypes t1 t2) $ zip fs1 fs2)
roCmpTypes (GenType (CS.TArray _ _ (Boxed True _) _) _ _) (GenType (CS.TArray _ _ (Boxed True _) _) _ _) = True
roCmpTypes (GenType (CS.TArray t1 _ sg1 _) _ _) (GenType (CS.TArray t2 _ sg2 _) _ _) =
    sg1 == sg2 && (roCmpTypes t1 t2)
roCmpTypes _ _ = False


-- Type selectors for components affected by making the type readonly.
-- Adjust to boxed, if unboxed array type
-- Make readonly, if container type is readonly

mkCmpType :: GCSigil -> GenType -> GenType
mkCmpType s t =
    let t' = if isUnboxedArrayType t then getBoxType t else t
    in if readonly s then mkReadonly t' else t'

delOrigInType :: GenType -> GenType
delOrigInType (GenType t _ s) = GenType t noOrigin s

-- Type of field, unitType if type does not have that field (or any field)
-- Origins in field types must be deleted, because they may not be present for uses of the field type.
-- Unboxed array types are adjusted to boxed.
getMemberType :: CCS.FieldName -> GenType -> GenType
getMemberType f (GenType (CS.TRecord _ fs s) _ _) =
    case find (\fld -> fst fld == f) fs of
         Nothing -> unitType
         Just (_,(t,_)) -> mkCmpType s $ delOrigInType t
-- maynull wrapped type
getMemberType f (GenType (CS.TCon n [t] _) _ _) | n == mapMayNull = getMemberType f t
-- other types -> unitType
getMemberType f _ = unitType

isUnboxedArrayMember :: CCS.FieldName -> GenType -> Bool
isUnboxedArrayMember f (GenType (CS.TRecord _ fs s) _ _) =
    case find (\fld -> fst fld == f) fs of
         Nothing -> False
         Just (_,(t,_)) -> isUnboxedArrayType t
isUnboxedArrayMember f (GenType (CS.TCon n [t] _) _ _) | n == mapMayNull = isUnboxedArrayMember f t
isUnboxedArrayMember _ _ = False

getBoxType :: GenType -> GenType
getBoxType (GenType (CS.TCon tn ts sg) o ms) = GenType (CS.TCon tn ts noSigil) o ms
getBoxType (GenType (CS.TRecord rp fs sg) o ms) = GenType (CS.TRecord rp fs noSigil) o ms
getBoxType (GenType (CS.TArray et e sg tk) o ms) = GenType (CS.TArray et e noSigil tk) o ms
getBoxType t = t

getNnlType :: GenType -> GenType
getNnlType (GenType (CS.TCon n [t] _) _ _) | n == mapMayNull = t
getNnlType t = t

-- Select referenced type for all possible translations of C pointer types.
-- Not applicable to encoded function pointer types.
getDerefType :: GenType -> GenType
-- void pointer
getDerefType (GenType (CS.TCon n [] _) _ _) | n == mapPtrVoid = unitType
-- explicit pointer (may have arbitrary type synonym)
getDerefType (GenType (CS.TRecord NonRec [(f,(t,_))] s) _ (Just _))
    | f == ptrDerivCompName = mkCmpType s t
-- maynull wrapped type
getDerefType (GenType (CS.TCon n [t] _) _ _) | n == mapMayNull = getDerefType t
-- array types -> element type
getDerefType (GenType (CS.TRecord NonRec [(f,((GenType (CS.TArray t _ _ _) _ _),_))] s) _ (Just _))
    | isArrDerivComp f = mkCmpType s t
getDerefType (GenType (CS.TCon n [t] s) _ _) | isArrDeriv n && not (arrDerivHasSize n) =
    mkCmpType s t
-- other types -> make unboxed
getDerefType t = mkUnboxed t

isUnboxedArrayDeref :: GenType -> Bool
isUnboxedArrayDeref (GenType (CS.TRecord NonRec [(f,(t,_))] s) _ (Just _))
    | f == ptrDerivCompName = isUnboxedArrayType t
isUnboxedArrayDeref (GenType (CS.TCon n [t] _) _ _) | n == mapMayNull = isUnboxedArrayDeref t
isUnboxedArrayDeref (GenType (CS.TRecord NonRec [(f,((GenType (CS.TArray t _ _ _) _ _),_))] s) _ (Just _))
    | isArrDerivComp f = isUnboxedArrayType t
isUnboxedArrayDeref (GenType (CS.TCon n [t] s) _ _) | isArrDeriv n && not (arrDerivHasSize n) =
    isUnboxedArrayType t
isUnboxedArrayDeref _ = False

-- | Type selectors for other components

getResultType :: GenType -> GenType
getResultType (GenType (CS.TFun _ rt) _ _) = rt

getParamType :: GenType -> GenType
getParamType (GenType (CS.TFun pt _) _ _) = pt

getLeadType :: GenType -> GenType
getLeadType (GenType (CS.TTuple (t : ts)) _ _) = t
getLeadType t = t

tupleSize :: GenType -> Int
tupleSize (GenType (CS.TTuple ts) _ _) = length ts
tupleSize _ = 1

-- | Type adaptation
-- Types which are compatible in C may be incompatible after translation to Cogent.
-- These will be adapted during postprocessing by converting one Cogent type to the other.
-- It is always possible to determine the resulting type from both Cogent types.
-- This is used for typing conditional expressions from the types of the branches.

adaptTypes :: GenType -> GenType -> GenType
-- for tuple types all components are adapted
adaptTypes t1@(GenType (CS.TTuple ts1) _ _) t2@(GenType (CS.TTuple ts2) _ _) =
    mkTupleType $ map (uncurry adaptTypes) $ zip ts1 ts2
-- String and char pointer is adapted to String
adaptTypes t1 t2 | isStringType t1 = t1
adaptTypes t1 t2 | isStringType t2 = t2
-- Bool and other type is adapted to Bool
adaptTypes t1 t2 | isBoolType t1 = t1
adaptTypes t1 t2 | isBoolType t2 = t2
-- Readonly and linear is adapted to readonly
adaptTypes t1 t2 | (not $ roCmpTypes t1 t2)
    && (not (isReadonly t1 && isReadonly t2)) = -- security check to prevent endless recursion
    adaptTypes (mkReadonly t1) (mkReadonly t2)
-- With and without MayNull is adapted to MayNull
adaptTypes t1 t2 | isMayNull t1 /= isMayNull t2 =
    adaptTypes (mkMayNull t1) (mkMayNull t2)
-- CVoidPtr is adapted to the specific pointer
adaptTypes t1 t2 | isVoidPtrType t1 = t2
adaptTypes t1 t2 | isVoidPtrType t2 = t1
-- U* is adapted to the larger type
adaptTypes t1@(GenType (CS.TCon n [] _) _ _) t2 | n == "U64" = t1
adaptTypes t1 t2@(GenType (CS.TCon n [] _) _ _) | n == "U64" = t2
adaptTypes t1@(GenType (CS.TCon n [] _) _ _) t2 | n == "U32" = t1
adaptTypes t1 t2@(GenType (CS.TCon n [] _) _ _) | n == "U32" = t2
adaptTypes t1@(GenType (CS.TCon n [] _) _ _) t2 | n == "U16" = t1
adaptTypes t1 t2@(GenType (CS.TCon n [] _) _ _) | n == "U16" = t2
-- In all other cases types should be compatible in Cogent
-- (i.e., only differ in origin or type synonyms).
adaptTypes t1 t2 = t1
