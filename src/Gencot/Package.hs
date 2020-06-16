{-# LANGUAGE PackageImports #-}
module Gencot.Package where

import System.IO (hPutStrLn, stderr, hPrint)
import qualified Data.Map as M (toList,Map,filter,elems,keys,filterWithKey)
import qualified Data.IntMap as IntMap (empty)
import Data.Map.Merge.Strict (merge,mapMissing,zipWithMatched)
import Data.List (sortBy,isPrefixOf,nub,(\\),union)
import qualified Data.Set as S (Set,filter,map,toList,unions)
import Data.Maybe (catMaybes,isJust)
import Control.Monad (liftM,when,foldM,mapM,sequence)

import "language-c" Language.C (CTranslUnit,CError,parseC,fileOfNode,CNode,nodeInfo,Ident,SUERef(AnonymousRef,NamedRef),isAnonymousRef,pretty,identToString)
import Language.C.Data.Position (initPos,posOf,posFile,posRow,isSourcePos)
import Language.C.Analysis
import Language.C.Analysis.DefTable (DefTable,DefTable(..),emptyDefTable,IdentEntry,TagEntry,globalDefs,lookupTag,lookupIdent)
import Language.C.Analysis.NameSpaceMap (NameSpaceMap,nameSpaceMap,defGlobal,globalNames)

import Gencot.Input (readFromFile_,readFromFile,getOwnDeclEvents)
import Gencot.Util.CallGraph (getCallGraph,CallGraph,getIdentInvokes)
import Gencot.Util.Types (TypeSet,TypeCarrier,TypeCarrierSet,carrierInTable,occurringTypes,transCloseTypes,selInAllTypes,selInContained,isLeafType,safeDeclLinkage)

readPackageFromInput_ :: IO [DefTable]
readPackageFromInput_ = do
    fnams <- (liftM ((filter (not . null)) . lines)) getContents
    when (null fnams) $ error "empty input package"
    mapM readFromFile_ fnams
    
readPackageFromInput :: s -> (DeclEvent -> Trav s ()) -> IO [(DefTable,s)]
readPackageFromInput uinit uhandler = do
    fnams <- (liftM ((filter (not . null)) . lines)) getContents
    when (null fnams) $ error "empty input package"
    mapM (readFromFile uinit uhandler) fnams
    
getIdentInvocations :: [CallGraph] -> IO [IdentDecl]
getIdentInvocations cgs = do
    {- get lists of declarations of invoked functions -}
    return $ S.toList $ S.unions $ map getIdentInvokes cgs

getOwnCallGraphs :: [DefTable] -> IO [CallGraph]
getOwnCallGraphs tables = do
    {- convert symbol tables to lists of declarations in processed files -}
    let decls = map (\tab -> getOwnDeclEvents (globalDefs tab) (\_ -> True)) tables
    {- get call graphs by traversing all function bodies in decls -}
    mapM (uncurry getCallGraph) $ zip tables decls

debugTable :: DefTable -> IO ()
debugTable = print . pretty . (filterGlobalDecls noBuiltin) . globalDefs

noBuiltin :: DeclEvent -> Bool
noBuiltin (DeclEvent d@(Declaration _)) | isPrefixOf "__" $ identToString $ declIdent d = False
noBuiltin _ = True

{--------}
foldTypeSets :: [TypeSet] -> DefTable -> TypeSet
foldTypeSets tss dt = filter (typeInTable dt) $ foldr union (head tss) (tail tss)

-- | Test whether directly contained tagless types are in the symbol table. 
typeInTable :: DefTable -> Type -> Bool
typeInTable dt t =
    all (anonInTable dt) $ filter anonTagType $ transCloseTypes selTypes [t]
    where selTypes = selInContained (not . isLeafType)
          anonInTable dt t = isJust $ lookupTag (getSUERef t) dt
{------------}
          
foldTypeCarrierSets :: [TypeCarrierSet] -> DefTable -> TypeCarrierSet
foldTypeCarrierSets tcss dt =
    (foldl union [] $ map (filter isLocalOrInternal) tcss)
    ++ (filter (carrierInTable dt) $ foldl union [] $ map (filter (not . isLocalOrInternal)) tcss)

isLocalOrInternal :: TypeCarrier -> Bool
isLocalOrInternal (LocalEvent _) = True
isLocalOrInternal (DeclEvent decl) = safeDeclLinkage decl == InternalLinkage
isLocalOrInternal _ = False

foldTables :: [DefTable] -> IO DefTable
foldTables tables = foldM combineTables (head tables) (tail tables)

combineTables :: DefTable -> DefTable -> IO DefTable
combineTables dt1 dt2 = do
    iDs <- combineIdentDecls (identDecls dt1) (identDecls dt2)
    tDs <- combineTagDecls (tagDecls dt1) (tagDecls dt2)
    return $ adjustTagless $ DefTable iDs tDs nameSpaceMap nameSpaceMap IntMap.empty IntMap.empty
          

combineIdentDecls :: NameSpaceMap Ident IdentEntry -> NameSpaceMap Ident IdentEntry -> IO (NameSpaceMap Ident IdentEntry)
combineIdentDecls m1 m2 = do
    cmap <- unionWithM selIdentEntry gm1 gm2
    return $ mkNameSpaceMap cmap
    where gm1 = M.filter notInternal $ globalNames m1
          gm2 = M.filter notInternal $ globalNames m2
          notInternal (Left _) = True
          notInternal (Right decl) = safeDeclLinkage decl /= InternalLinkage

selIdentEntry :: Ident -> IdentEntry -> Maybe IdentEntry -> IO IdentEntry
selIdentEntry k res Nothing = return res
selIdentEntry k res@(Left t1) (Just (Left t2)) = do
    when (not $ samePos t1 t2) $ hPutStrLn stderr $ "Warning: different type definitions for " ++ identToString k
    return res
selIdentEntry k res@(Right dec1) (Just (Right dec2)) | isDef dec1 && isDef dec2 = do
    when (not $ samePos dec1 dec2) $ hPutStrLn stderr $ "Warning: different object/function/enumerator definitions for: " ++ identToString k
    return res
selIdentEntry _ res@(Right dec1) (Just (Right dec2)) | isDef dec1 = return res
selIdentEntry _ (Right dec1) (Just res@(Right dec2)) | isDef dec2 = return res
selIdentEntry _ res@(Right dec1) (Just (Right dec2)) = return res
selIdentEntry k res _ = do
    hPutStrLn stderr $ "Warning: Defined as type and object: " ++ identToString k
    return res

isDef (Declaration _) = False
isDef _ = True

samePos :: CNode n => n -> n -> Bool
samePos n1 n2 = 
    if isSourcePos p1 && isSourcePos p2 
       then (posFile p1) == (posFile p2) &&
            (posFile p1) /= "<stdin>" &&
            (posRow p1) == (posRow p2)
       else p1 == p2
    where p1 = posOf $ nodeInfo n1
          p2 = posOf $ nodeInfo n2

unionWithM :: Ord k => (k -> a -> Maybe a -> IO a) -> M.Map k a -> M.Map k a -> IO (M.Map k a)
unionWithM cmb m1 m2 = 
    mapM ucmb $ merge (mapMissing g) (mapMissing g) (zipWithMatched f) m1 m2
    where f :: k -> a -> a -> (k,a,Maybe a)
          f key a1 a2 = (key,a1,Just a2)
          g :: k -> a -> (k,a,Maybe a)
          g key val = (key,val,Nothing)
          ucmb (key,v1,v2) = cmb key v1 v2

mkNameSpaceMap :: Ord k => M.Map k a -> NameSpaceMap k a
mkNameSpaceMap m = foldl (\nsm (i,e) -> fst $ defGlobal nsm i e) nameSpaceMap $ M.toList m

combineTagDecls :: NameSpaceMap SUERef TagEntry -> NameSpaceMap SUERef TagEntry -> IO (NameSpaceMap SUERef TagEntry)
combineTagDecls m1 m2 = do
    cmap <- unionWithM selTagEntry (globalNames m1) (globalNames m2)
    return $ mkNameSpaceMap cmap

selTagEntry :: SUERef -> TagEntry -> Maybe TagEntry -> IO TagEntry
selTagEntry (AnonymousRef _) res@(Right t1) (Just other@(Right t2)) = do
    when (not $ samePos t1 t2) $ do
        hPutStrLn stderr $ "Warning: collision of internal identifier for tagless types:"
        hPrint stderr $ pretty res
        hPrint stderr $ pretty other
        hPutStrLn stderr $ "To solve this, specify a tag for at least one of them."
    return res
selTagEntry (NamedRef idnam) res@(Right t1) (Just other@(Right t2)) = do
    when (not $ samePos t1 t2) $ do
        hPutStrLn stderr ("Error: same tag \"" ++ (identToString idnam) ++ "\" used for different types:")
        hPrint stderr $ pretty res
        hPrint stderr $ pretty other
        hPutStrLn stderr $ "To solve this, rename one of them."
    return res
selTagEntry _ res _ = return res

adjustTagless :: DefTable -> DefTable
adjustTagless dt = if null ua then dt else removeTagDefs ua dt
    where ua = unusedAnon dt

-- | Tagless SUERefs which are not referenced.
unusedAnon :: DefTable -> [SUERef]
unusedAnon dt@(DefTable iDs tDs _ _ _ _) = anonRefs \\ usedAnon
    where anonRefs = filter isAnonymousRef $ M.keys $ globTags
          -- used tagless type references. 
          -- Starting with all types but the tagless types themselves we calculate the transitive closure
          -- of type usage and select the tagless types. Tagless types used by an unused tagless type are not
          -- contained, thus they need not be determined seperately.
          usedAnon = map getSUERef $ filter anonTagType $ transCloseTypes selTypes $ nub $ concat $ (tDtypes ++ iDtypes)
          -- tDtypes are all struct/union/enum types with a tag
          tDtypes = map occTypes $ filter (not . anonTagEvent) $ catMaybes $ map mkTagEvent $ M.elems $ globTags
          -- iDtypes are the types in all object declarations and definitions
          iDtypes = map (occTypes . mkIdentEvent) $ M.elems $ globalNames iDs
          globTags = globalNames tDs
          selTypes = selInAllTypes dt (not . isLeafType)
          occTypes = occurringTypes (not . isLeafType)

mkIdentEvent :: IdentEntry -> DeclEvent
mkIdentEvent (Left td) = TypeDefEvent td
mkIdentEvent (Right decl) = DeclEvent decl

mkTagEvent :: TagEntry -> Maybe DeclEvent
mkTagEvent (Left _) = Nothing
mkTagEvent (Right td) = Just $ TagEvent td

anonTagType (DirectType (TyComp r) _ _) = isAnonymousRef $ sueRef r
anonTagType (DirectType (TyEnum r) _ _) = isAnonymousRef $ sueRef r
anonTagType _ = False

anonTagEvent (TagEvent td) = isAnonymousRef $ sueRef td
anonTagEvent _ = False

getSUERef (DirectType (TyComp r) _ _) = sueRef r
getSUERef (DirectType (TyEnum r) _ _) = sueRef r

removeTagDefs :: [SUERef] -> DefTable -> DefTable
removeTagDefs ua (DefTable iDs tDs lDs mDs rT tT) = DefTable iDs res lDs mDs rT tT
    where res = mkNameSpaceMap $ M.filterWithKey (\k _ -> k `notElem` ua) $ globalNames tDs
