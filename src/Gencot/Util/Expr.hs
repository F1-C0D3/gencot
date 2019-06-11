{-# LANGUAGE PackageImports, TypeSynonymInstances, FlexibleInstances #-}
module Gencot.Util.Expr where

import Data.Set as S
import Control.Monad (liftM)

import "language-c" Language.C as LC hiding (pretty,Pretty)
import Language.C.Analysis as LCA
import Language.C.Data.Ident as LCI
import qualified Language.C.Analysis.DefTable as LCD
import Language.C.Analysis.TravMonad (MonadTrav)

import Gencot.Util.Types (resolveTypedef,getCompType,getMemberDecl)

-- | Return the root identifier in the expression, if there is one.
getRootIdent :: LC.CExpr -> Maybe LCI.Ident
getRootIdent (LC.CVar nam _) = Just nam
getRootIdent (LC.CCast _ expr _) = getRootIdent expr
getRootIdent (LC.CUnary LC.CIndOp expr _) = getRootIdent expr
getRootIdent (LC.CIndex expr1 expr2 _) = getRootIdent expr1
getRootIdent (LC.CMember expr _ _ _) = getRootIdent expr
getRootIdent _ = Nothing

-- | Test whether an expression includes at least one derefence operation.
isReference :: LC.CExpr -> Bool
isReference (LC.CUnary LC.CIndOp _ _) = True
isReference (LC.CMember _ _ True n) = True
isReference (LC.CCast _ expr _) = isReference expr
isReference (LC.CIndex expr _ _) = isReference expr
isReference (LC.CMember expr _ _ _) = isReference expr
isReference _ = False

getType :: MonadTrav m => LC.CExpr -> m (Maybe LCA.Type)
getType (LC.CMember expr mid isRef _) = do
    mtyp <- getType expr
    case mtyp of 
         Nothing -> return Nothing
         Just typ -> do
             dt <- LCA.getDefTable
             case getMemberDecl (getCompType typ dt) mid of
                  Nothing -> return Nothing
                  Just mdecl -> return $ Just $ LCA.declType mdecl
getType (LC.CVar sid _) = do
    msdecl <- LCA.lookupObject sid
    case msdecl of
         Nothing -> return Nothing
         Just decl -> return $ Just $ LCA.declType decl
getType _ = return Nothing 

