module Main where
import System.IO (hPutStrLn, stderr)
import Data.ByteString (getContents)
import Data.Map (toList)
import Data.List (sortBy)
import Text.PrettyPrint.HughesPJ

import Language.C (parseC,initPos,fileOfNode,pretty,Pretty,posOf,Pos, Position,posRow)
import Language.C.Analysis

main :: IO ()
main = do
  input_stream <- Data.ByteString.getContents
  ast <- errorOnLeft "Parse Error" $ parseC input_stream (initPos "<stdin>")
--  (globals,warnings) <- errorOnLeft "Semantic Error" $ runTrav_ $ analyseAST ast
  globals <- either (error . show) (return . fst) $ runTrav_ $ analyseAST ast

--  mapM (hPutStrLn stderr . show) warnings
  print $ pretty $ procGlobals $ filterGlobalDecls (maybe False ((==) "<stdin>") . fileOfNode) globals


errorOnLeft :: (Show a) => String -> (Either a b) -> IO b
errorOnLeft msg = either (error . ((msg ++ ": ")++).show) return

procGlobals gmap = sortBy compItem $
    map (IdentDeclaration . snd) (toList $ gObjs gmap) ++
    map (TagDefinition . snd) (toList $ gTags gmap) ++
    map (TypeDefinition .snd) (toList $ gTypeDefs gmap)

instance Pretty a => Pretty [a] where
    pretty idlist = brackets (vcat $ map pretty idlist)

data CItem = IdentDeclaration IdentDecl
           | TagDefinition TagDef
           | TypeDefinition TypeDef
instance Pretty CItem where
    pretty (IdentDeclaration id) = pretty id
    pretty (TagDefinition td) = pretty td
    pretty (TypeDefinition td) = pretty td

instance Pos CItem where
    posOf (IdentDeclaration id) = posOf id
    posOf (TagDefinition td) = posOf td
    posOf (TypeDefinition td) = posOf td

compItem :: CItem -> CItem -> Ordering
compItem ci1 ci2 = compare (posOf ci1) (posOf ci2)
    
