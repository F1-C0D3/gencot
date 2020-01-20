{-# LANGUAGE PackageImports #-}
module Gencot.Items where

import System.FilePath (takeExtension,takeFileName,takeBaseName)

import Language.C.Data.Ident as LCI
import Language.C.Data.Node as LCN
import Language.C.Analysis as LCA
 
-- | Construct the identifier for an individual toplevel item.
-- An individual toplevel item is a function or a global object (variable).
-- It is specified by its declaration. 
-- The second parameter is the main source file name to be used instead of <stdin>.
getIndividualItemId :: LCA.IdentDecl -> String -> String
getIndividualItemId idec sfn = (linkagePrefix idec sfn) ++ (LCI.identToString $ LCA.declIdent idec)

-- | The prefix to be prepended to an item identifier if the item has internal linkage.
-- The item is specified by its declaration. 
-- The second parameter is the main source file name to be used instead of <stdin>.
linkagePrefix :: (LCA.Declaration d, LCN.CNode d) => d -> String -> String
linkagePrefix idec sfn | isInternal idec = prefix ++ ":"
    where fn = case LCN.fileOfNode idec of
                    Nothing -> "<unknown>"
                    Just res -> takeFileName res
          fn' = if fn == "<stdin>" then sfn else fn
          prefix = if (takeExtension fn') == ".c" then (takeBaseName fn') else (takeFileName fn')
          isInternal idec = 
            case LCA.declStorage idec of
                 NoStorage -> False -- function pointer struct members
                 _ -> LCA.declLinkage idec == LCA.InternalLinkage
linkagePrefix _ _ = ""

-- | Construct the identifier for a collective item specified by a typedef name.
getTypedefItemId :: LCI.Ident -> String
getTypedefItemId idnam = "typedef|" ++ (LCI.identToString idnam)

-- | Construct the identifier for a collective item specified by a compound tag name.
getTagItemId :: LCI.SUERef -> LCA.CompTyKind -> String
getTagItemId (LCI.AnonymousRef _) knd = (kndstr knd) ++ "|<anonymous>"
getTagItemId (LCI.NamedRef idnam) knd = (kndstr knd) ++ "|" ++ (LCI.identToString idnam)

kndstr LCA.StructTag = "struct"
kndstr LCA.UnionTag = "union"

-- | Construct the identifier for a collective item specified by an enum tag name.
getEnumItemId :: LCI.SUERef -> String
getEnumItemId (LCI.AnonymousRef _) knd = "enum|<anonymous>"
getEnumItemId (LCI.NamedRef idnam) knd = "enum|" ++ (LCI.identToString idnam)

-- | Construct the identifier for a member subitem of an item of struct or union type.
-- The first parameter is the identifier of the main item.
getMemberSubItemId :: String -> LCA.MemberDecl -> String
getMemberSubItemId item mdecl = 
    item ++ "." ++ (LCI.identToString $ LCA.declIdent mdecl)

-- | Construct the identifier for the element subitem of an item of array type.
getElemSubItemId :: String -> String
getElemSubItemId item = item ++ "/[]"

-- | Construct the identifier for the referenced data subitem of an item of pointer type.
getRefSubItemId :: String -> String
getRefSubItemId item = item ++ "/*"

-- | Construct the identifier for the result subitem of an item of function type.
getResultSubItemId :: String -> String
getResultSubItemId item = item ++ "/()"

-- | Construct the identifier for a parameter subitem of an item of function type.
-- The first parameter is the identifier of the main item.
getParamSubItemId :: String -> LCA.ParamDecl -> String
getParamSubItemId item pdecl = 
    item ++ "/" ++ (LCI.identToString $ LCA.declIdent pdecl)

-- | Retrieve an item's type together with the item identifier.
-- The item is specified as a TypeCarrier
-- The additional first parameter is the source file name of the main source file.
-- The additional second parameter is a set of typedef names where to stop resolving external types.
-- The result is a singleton list or empty. 
-- LocalEvent and ParamEvent items are not processed because they correspond to function sub-items.
-- Tagless struct items are not processed because they are not type carriers themselves.
carriedWithItemId :: String -> [String] -> TypeCarrier -> [(String,LCA.Type)]
carriedWithItemId sfn _ (LCA.DeclEvent idecl) = 
    [(getIndividualItemId decl sfn, LCA.declType decl)]
carriedWithItemId _ tdn (LCA.TypeDefEvent td@(LCA.TypeDef idnam t _ _)) | isExtern td = 
    [(getTypedefItemId idnam, resolveFully tdn t)]
carriedWithItemId _ _ (LCA.TypeDefEvent td@(LCA.TypeDef idnam t _ _)) = 
    [(getTypedefItemId idnam, t)]
carriedWithItemId _ _ (LCA.TagEvent def@(LCA.CompDef (LCA.CompType sueref knd _ _ _))) | LCI.isAnonymousRef sueref = []
carriedWithItemId _ _ (LCA.TagEvent def@(LCA.CompDef (LCA.CompType sueref knd _ _ _))) =
    [(getTagItemId sueref knd, 
    nub $ map (\md -> typeWithFunId (getFunMemberId ref md) $ LCA.declType md) mems
    where ref = sueRef def
carriedWithItemId _ _ (LCA.LocalEvent decl) = [("",LCA.declType decl)]
carriedWithItemId _ _ (LCA.ParamEvent decl) = [("",LCA.declType decl)]
carriedWithItemId _ _ _ = []

carriedInFunction :: String -> LCA.Type -> [(String,LCA.Type)]
carriedInFunction fid (LCA.FunctionType (LCA.FunType rt pars _) _) =
    nub (("",rt) : map (\pd -> typeWithFunId (getLocalFunId fid pd) $ LCA.declType pd) pars)
carriedInFunction fid (LCA.FunctionType (LCA.FunTypeIncomplete rt) _) = [("",rt)]
carriedInFunction _ _ = []

typeWithFunId :: String -> LCA.Type -> (String, LCA.Type)
typeWithFunId fid t | getsParmodDescr t = (fid,t)
typeWithFunId _ t = ("",t)

