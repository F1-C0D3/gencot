module Gencot.Util.Properties where

import Data.List (break,lines,words,union,intercalate)
import Data.Map (Map,singleton,unions,unionWith,toAscList)
import Data.Char (isSpace)

-- | Mapping from item ids to lists of property strings.
-- Used property strings are: nn, ro, ns, mf, hu, dp, rp
type ItemProperties = Map String [String]

-- | Read an item property map from stdin.
readPropertiesFromInput :: IO ItemProperties
readPropertiesFromInput = do
    inp <- getContents
    return $ parseProperties inp

-- | Read an item property map from a file.
readPropertiesFromFile :: FilePath -> IO ItemProperties
readPropertiesFromFile file = do 
    inp <- readFile file 
    return $ parseProperties inp

-- | Parse the string representation of a property map 
-- It consists of a sequence of lines where each line specifies properties for a single item.
parseProperties :: String -> ItemProperties
parseProperties inp = 
    unions $ map parsePropertyLine $ lines inp

-- | Parse a property specification for a single item.
-- It has the form <item id>[:] <whitespace> <property> <whitespace> ...
parsePropertyLine :: String -> ItemProperties
parsePropertyLine line =
    singleton iid props
    where (ciid,rest) = break isSpace line -- ciid = <item id>[:], rest = <whitespace> <property> <whitespace> ...
          iid = if last ciid == ':' then init ciid else ciid -- iid = <item id>
          props = words rest -- [<property>,...]

-- | Output an item property map as a sequence of lines.
-- Reverse of @parseProperties@
showProperties :: ItemProperties -> String
showProperties ipm = 
    unlines $ map showPropertyLine $ toAscList ipm

-- | Output the property declarations for a single item as a single line.
showPropertyLine :: (String,[String]) -> String
showPropertyLine (iid,props) =
    iid ++ ": " ++ (intercalate " " props)

-- | Combine two property maps. 
-- If an item occurs in both maps its declared properties are united.
combineProperties :: ItemProperties -> ItemProperties -> ItemProperties
combineProperties ipm1 ipm2 = unionWith union ipm1 ipm2
