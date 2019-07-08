{-# LANGUAGE PackageImports #-}
module Gencot.SymTab where

import System.IO (hPutStrLn, stderr)
import qualified Data.Map as M (toList,Map,filter,elems,keys,filterWithKey)
import qualified Data.IntMap as IntMap (empty)
import Data.Map.Merge.Strict (merge,mapMissing,zipWithMatched)
import Data.List (sortBy,isPrefixOf,nub,(\\))
import qualified Data.Set as S (Set,filter,map)
import Data.Maybe (catMaybes)
import Control.Monad (liftM,when,foldM,mapM,sequence)

import "language-c" Language.C (CTranslUnit,CError,parseC,fileOfNode,Ident,SUERef(AnonymousRef),isAnonymousRef,pretty,identToString)
import Language.C.Data.Position (initPos,posOf,posFile,posRow,isSourcePos)
import Language.C.Analysis
import Language.C.Analysis.DefTable (DefTable,DefTable(..),emptyDefTable,IdentEntry,TagEntry,globalDefs)
import Language.C.Analysis.NameSpaceMap (NameSpaceMap,nameSpaceMap,defGlobal,globalNames)

import Gencot.Input (readFromFile_)
import Gencot.Util.Types (occurringTypes,transCloseTypes,selInAllTypes,isLeafType)

debugTable :: DefTable -> IO ()
debugTable = print . pretty . (filterGlobalDecls noBuiltin) . globalDefs

noBuiltin :: DeclEvent -> Bool
noBuiltin (DeclEvent d@(Declaration _)) | isPrefixOf "__" $ identToString $ declIdent d = False
noBuiltin _ = True

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
          notInternal (Right decl) = declLinkage decl /= InternalLinkage

selIdentEntry :: Ident -> IdentEntry -> Maybe IdentEntry -> IO IdentEntry
selIdentEntry k res Nothing = return res
selIdentEntry k res@(Left (TypeDef _ _ _ n1)) (Just (Left (TypeDef _ _ _ n2))) = do
    when (not $ samePos n1 n2) $ putStrLn $ "Warning: different definitions for " ++ identToString k
    return res
    where samePos n1 n2 = 
            let p1 = posOf n1
                p2 = posOf n2
            in if isSourcePos p1 && isSourcePos p2 
                  then (posFile p1) == (posFile p2) &&
                       (posFile p1) /= "<stdin>" &&
                       (posRow p1) == (posRow p2)
                  else p1 == p2
selIdentEntry k res@(Right dec1) (Just (Right dec2)) | isDef dec1 && isDef dec2 = do
    putStrLn $ "Warning: different definitions for: " ++ identToString k
    return res
selIdentEntry _ res@(Right dec1) (Just (Right dec2)) | isDef dec1 = return res
selIdentEntry _ (Right dec1) (Just res@(Right dec2)) | isDef dec2 = return res
selIdentEntry _ res@(Right dec1) (Just (Right dec2)) = return res
selIdentEntry k res _ = do
    putStrLn $ "Warning: Defined as type and object: " ++ identToString k
    return res

isDef (Declaration _) = False
isDef _ = True

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
selTagEntry (AnonymousRef _) res (Just other) = do
    putStrLn $ "Warning: collision of internal identifier for tagless types:"
    print $ pretty res
    print $ pretty other
    putStrLn $ "To solve this, specify a tag for at least one of them."
    return res
selTagEntry _ res _ = return res

adjustTagless :: DefTable -> DefTable
adjustTagless dt = if null ua then dt else removeTagDefs ua dt
    where ua = unusedAnon dt

-- | Tagless SUERefs which are not referenced.
-- 
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
