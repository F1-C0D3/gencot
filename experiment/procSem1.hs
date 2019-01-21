{-# LANGUAGE PackageImports #-}
module Main where
import System.IO (hPutStrLn, stderr)
import Data.ByteString (getContents)
import Data.Map (toList,elems,mapKeys,filterWithKey, Map)
import Data.List (sortBy)
import Text.PrettyPrint.HughesPJ

import "language-c" Language.C (parseC,initPos,fileOfNode,pretty,Pretty,posOf,SUERef(..),isAnonymousRef,Ident)
import Language.C.Analysis

main :: IO ()
main = do
  input_stream <- Data.ByteString.getContents
  ast <- errorOnLeft "Parse Error" $ parseC input_stream (initPos "<stdin>")
  (globals,warnings) <- errorOnLeft "Semantic Error" $ runTrav_ $ analyseAST ast
  mapM (hPutStrLn stderr . show) warnings

  print $ pretty $ sortBy compEvent $ listGlobals $ filterGlobals globals


errorOnLeft :: (Show a) => String -> (Either a b) -> IO b
errorOnLeft msg = either (error . ((msg ++ ": ")++).show) return

listGlobals :: GlobalDecls -> [DeclEvent]
listGlobals gmap = 
    concat $ map elems $ wraps <*> [gmap]
    where wraps = [(fmap DeclEvent) . gObjs, 
                   (fmap TagEvent) . prepTags, 
                   (fmap TypeDefEvent) . gTypeDefs]

prepTags :: GlobalDecls -> Map Ident TagDef
prepTags gmap = 
    mapKeys (\(NamedRef i)-> i) 
    $ filterWithKey (\k _ -> not $ isAnonymousRef k) $ gTags gmap

filterGlobals :: GlobalDecls -> GlobalDecls
filterGlobals gmap = 
    filterGlobalDecls (maybe False ((==) "<stdin>") . fileOfNode) gmap

compEvent :: DeclEvent -> DeclEvent -> Ordering
compEvent ci1 ci2 = compare (posOf ci1) (posOf ci2)

instance Pretty a => Pretty [a] where
    pretty idlist = brackets (vcat $ map pretty idlist)

instance Pretty DeclEvent where
    pretty (DeclEvent id) = pretty id
    pretty (TagEvent td) = pretty td
    pretty (TypeDefEvent td) = pretty td
    pretty _ = empty

    
