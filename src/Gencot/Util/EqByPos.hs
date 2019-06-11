{-# LANGUAGE PackageImports, TypeSynonymInstances, FlexibleInstances #-}
module Gencot.Util.EqByPos where

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
