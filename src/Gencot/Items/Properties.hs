module Gencot.Items.Properties where

import Data.List (break,lines,words,union,intercalate,nub,(\\),find,isPrefixOf)
import Data.Map (Map,singleton,unions,unionWith,differenceWith,toAscList,keys,filterWithKey)
import qualified Data.Map as M (map)
import Data.Char (isSpace,isLetter)

import Gencot.Items.Identifier (toplevelItemId)

-- | Mapping from item ids to lists of property strings.
-- Used property strings are: nn, ro, ns, io, hu, gs, ar, cv
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
    unions $ map parsePropertyLine $ ((filter (any isLetter)) . lines) inp

-- | Parse a property specification for a single item.
-- It has the form <item id>[:] <whitespace> [-]<property> <whitespace> ...
parsePropertyLine :: String -> ItemProperties
parsePropertyLine line =
    singleton iid props
    where (ciid,rest) = break isSpace line -- ciid = <item id>[:], rest = <whitespace> [-]<property> <whitespace> ...
          iid = if last ciid == ':' then init ciid else ciid -- iid = <item id>
          props = reduceGS $ nub $ words rest -- [[-]<property>,...]

-- | Reduce gs<i> properties to the first and omit all others.
reduceGS :: [String] -> [String]
reduceGS props = 
    case firstGS of
         Nothing -> props
         (Just gs) -> filter (\w -> (not ("gs" `isPrefixOf` w)) || w == gs) props
    where firstGS = find (\w -> "gs" `isPrefixOf` w) props

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
combineProperties ipm1 ipm2 = 
    differenceWith (\ps1 ps2 -> Just (ps1 \\ ps2)) (unionWith union ipm1 (selpositive ipm2)) (selnegative ipm2)
    where selpositive ipm = M.map (filter (\w -> (not ("-" `isPrefixOf` w)))) ipm
          selnegative ipm = M.map (\l -> map tail $ filter (\w -> ("-" `isPrefixOf` w)) l) ipm

-- | List of all toplevel item ids used in a property map.
getToplevelItemIds :: ItemProperties -> [String]
getToplevelItemIds ipm = nub $ map toplevelItemId $ keys ipm

-- | Filter an item property map according to item identifier prefixes.
filterItemsPrefixes :: [String] -> ItemProperties -> ItemProperties
filterItemsPrefixes prefs ipm = filterWithKey (keyHasPrefix prefs) ipm
    where keyHasPrefix prefs k _ = elem (toplevelItemId k) prefs
