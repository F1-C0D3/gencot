module Gencot.Util.Properties where

import Data.List (break, lines, words)
import Data.Map (singleton,unions)
import Data.Char (isSpace)
import Gencot.Traversal (ItemProperties)

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
