{-# LANGUAGE PackageImports, TypeSynonymInstances, FlexibleInstances #-}
module Gencot.Util.Equality where

import "language-c" Language.C as LC
import Language.C.Data.Node as LCN
import Language.C.Data.Position as LCP
import qualified Language.C.Analysis as LCA

instance Eq LCA.FunDef where
    fd1 == fd2 = (posOf fd1) == (posOf fd2)

instance Ord LCA.FunDef where
    compare fd1 fd2 = compare (posOf fd1) (posOf fd2)

instance Eq LCA.IdentDecl where
    id1 == id2 = (posOf id1) == (posOf id2)

instance Ord LCA.IdentDecl where
    compare id1 id2 = compare (posOf id1) (posOf id2)

-- | Equality for types. Attributes are ignored.
instance Eq LCA.Type where
    (LCA.DirectType tn1 q1 _) == (LCA.DirectType tn2 q2 _) = tn1 == tn2 && q1 == q2
    (LCA.PtrType t1 q1 _) == (LCA.PtrType t2 q2 _) = t1 == t2 && q1 == q2
    (LCA.ArrayType t1 (LCA.UnknownArraySize s1) q1 _) == (LCA.ArrayType t2 (LCA.UnknownArraySize s2) q2 _) =
        t1 == t2 && s1 == s2 && q1 == q2
    (LCA.ArrayType t1 (LCA.ArraySize s1 e1) q1 _) == (LCA.ArrayType t2 (LCA.ArraySize s2 e2) q2 _) =
        t1 == t2 && s1 == s2 && q1 == q2 && e1 == e2
    (LCA.FunctionType (LCA.FunType t1 pars1 isVar1) _) == (LCA.FunctionType (LCA.FunType t2 pars2 isVar2) _) =
        t1 == t2 && isVar1 == isVar2 && 
        (and $ map (uncurry (==)) $ zip (map LCA.declType pars1) (map LCA.declType pars2))
    (LCA.TypeDefType (LCA.TypeDefRef i1 _ _) q1 _) == (LCA.TypeDefType (LCA.TypeDefRef i2 _ _) q2 _) =
        i1 == i2 && q1 == q2
    _ == _ = False

instance Eq LCA.TypeName where
    LCA.TyVoid == LCA.TyVoid = True
    (LCA.TyIntegral it1) == (LCA.TyIntegral it2) = it1 == it2
    (LCA.TyFloating ft1) == (LCA.TyFloating ft2) = ft1 == ft2
    (LCA.TyComplex ft1) == (LCA.TyComplex ft2) = ft1 == ft2
    (LCA.TyComp (LCA.CompTypeRef r1 k1 _)) == (LCA.TyComp (LCA.CompTypeRef r2 k2 _)) = r1 == r2 && k1 == k2
    (LCA.TyEnum (LCA.EnumTypeRef r1 _)) == (LCA.TyEnum (LCA.EnumTypeRef r2 _)) = r1 == r2
    (LCA.TyBuiltin LCA.TyVaList) == (LCA.TyBuiltin LCA.TyVaList) = True
    (LCA.TyBuiltin LCA.TyAny) == (LCA.TyBuiltin LCA.TyAny) = True
    _ == _ = False

-- | Equality for expressions. For constants values are compared.
-- Otherwise the expressions must be the same (at the same position in the source file).
instance Eq LC.CExpr where
    (LC.CConst (LC.CIntConst i1 _)) == (LC.CConst (LC.CIntConst i2 _)) = i1 == i2
    (LC.CConst (LC.CCharConst c1 _)) == (LC.CConst (LC.CCharConst c2 _)) = c1 == c2
    (LC.CConst (LC.CFloatConst f1 _)) == (LC.CConst (LC.CFloatConst f2 _)) = f1 == f2
    (LC.CConst (LC.CStrConst s1 _)) == (LC.CConst (LC.CStrConst s2 _)) = s1 == s2
    e1 == e2 = (posOf e1) == (posOf e2)
    
