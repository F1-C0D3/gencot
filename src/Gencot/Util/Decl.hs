{-# LANGUAGE PackageImports, TypeSynonymInstances, FlexibleInstances #-}
module Gencot.Util.Decl where

import Data.Set as S (Set,empty,union,unions,insert,filter,toList,fromList,map)
import Data.Foldable (foldlM,find)
import Control.Monad (liftM,liftM2,when)
import Data.Maybe (isJust)

import "language-c" Language.C as LC
import Language.C.Data.Ident as LCI
import Language.C.Data.Node as LCN
import Language.C.Data.Position as LCP
import Language.C.Syntax.AST as LCS
import Language.C.Analysis as LCA
import qualified Language.C.Analysis.DefTable as LCD
import Language.C.Analysis.TravMonad (MonadTrav,Trav,runTrav,travErrors,getUserState)
import Language.C.Analysis.TypeUtils (isFunctionType)

type CIDecl = (Maybe LC.CDeclr,Maybe LC.CInit, Maybe LC.CExpr)

-- | Traverse the declarators of a local declaration with an action and a folding function.
-- For every declarator, first the action is executed, then the declarator is analysed and added to the symbol table.
-- The result is the fold of the results of all actions.
-- This function is mainly an adapted and extended copy of Language.C.Analysis.AstAnalysis.analyseDecl.
traverseLocalDecl :: (MonadTrav m) => LC.CDecl -> (CIDecl -> m r) -> ([r] -> r) -> m r
traverseLocalDecl (CStaticAssert _ _ _) a _ = a (Nothing,Nothing,Nothing)
traverseLocalDecl decl@(CDecl declspecs declrs node) action foldfun
    | null declrs = action (Nothing,Nothing,Nothing)
    | (Just declspecs') <- typedef_spec = liftM foldfun $ mapM (uncurry (analyseTyDef declspecs')) declr_list
    | otherwise   = do let (storage_specs, attrs, typequals, typespecs, funspecs, _alignspecs) =
                             partitionDeclSpecs declspecs
                       canonTySpecs <- LCA.canonicalTypeSpec typespecs
                       let specs =
                             (storage_specs, attrs, typequals, canonTySpecs, funspecs)
                       liftM foldfun $ mapM (uncurry (analyseVarDeclr specs)) declr_list
    where
    declr_list = zip (True : repeat False) declrs
    typedef_spec = hasTypeDef declspecs

    analyseTyDef declspecs' handle_sue_def d@(Just tydeclr, Nothing , Nothing) = do
        res <- action d
        analyseTypeDef handle_sue_def declspecs' tydeclr node
        return res

    analyseVarDeclr specs handle_sue_def d@(Just declr, init_opt, Nothing) = do
        res <- action d
        -- analyse the declarator
        let (storage_specs, attrs, typequals, canonTySpecs, inline) = specs
        vardeclInfo@(LCA.VarDeclInfo _ _ _ _ typ _) <-
          LCA.analyseVarDecl handle_sue_def storage_specs attrs typequals canonTySpecs inline
                         declr [] Nothing
        -- declare / define the object
        if isFunctionType typ
            then return ()  -- ignore local functions
            else localVarDecl vardeclInfo init_opt
        return res

-- All following functions have been copied from Language.C.Analysis.AstAnalysis
------------------------

hasTypeDef :: [CDeclSpec] -> Maybe [CDeclSpec]
hasTypeDef declspecs =
    case foldr hasTypeDefSpec (False,[]) declspecs of
        (True,specs') -> Just specs'
        (False,_)     -> Nothing
    where
    hasTypeDefSpec (CStorageSpec (CTypedef _)) (_,specs) = (True, specs)
    hasTypeDefSpec spec (b,specs) = (b,spec:specs)

analyseTypeDef :: (MonadTrav m) => Bool -> [CDeclSpec] -> CDeclr -> NodeInfo -> m ()
analyseTypeDef handle_sue_def declspecs declr node_info = do
    -- analyse the declarator
    (VarDeclInfo name fun_attrs storage_spec attrs ty _node) <- analyseVarDecl' handle_sue_def declspecs declr [] Nothing
    checkValidTypeDef fun_attrs storage_spec attrs
    when (isNoName name) $ astError node_info "NoName in analyseTypeDef"
    let ident = identOfVarName name
    handleTypeDef (TypeDef ident ty attrs node_info)
    where
    checkValidTypeDef fun_attrs  _ _ | fun_attrs /= noFunctionAttrs =
                                         astError node_info "inline specifier for typeDef"
    checkValidTypeDef _ NoStorageSpec _ = return ()
    checkValidTypeDef _ bad_storage _ = astError node_info $ "storage specified for typeDef: " ++ show bad_storage

localVarDecl :: (MonadTrav m) => VarDeclInfo -> Maybe Initializer -> m ()
localVarDecl (VarDeclInfo var_name fun_attrs storage_spec attrs typ node_info) init_opt =
    do when (isNoName var_name) $ astError node_info "NoName in localVarDecl"
       (storage,is_def) <- localStorage storage_spec
       let vardecl = VarDecl var_name (DeclAttrs fun_attrs storage attrs) typ
       if is_def
           then handleObjectDef True ident (ObjDef vardecl init_opt node_info)
           else handleVarDecl True (Decl vardecl node_info)
    where
    ident = identOfVarName var_name
    localStorage NoStorageSpec = return (Auto False,True)
    localStorage ThreadSpec    = return (Auto True,True)
    localStorage RegSpec = return (Auto True,True)
    -- static no linkage
    localStorage (StaticSpec thread_local) =
      return (Static NoLinkage thread_local,True)
    localStorage (ExternSpec thread_local)
      | isJust init_opt = astError node_info "extern keyword and initializer for local"
      | otherwise =
          do old_decl <- lookupObject ident
             return (maybe (Static ExternalLinkage thread_local) declStorage old_decl,False)
    localStorage _ = astError node_info "bad storage specifier for local"
