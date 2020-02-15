{-# LANGUAGE PackageImports #-}
module Gencot.Items.Identifier where

import Data.Char (isDigit,isLetter)
import Data.List (break,elemIndex,dropWhileEnd)

-- | For an item identifier get the identifier of the toplevel item.
-- This is always a prefix of the item identifier.
toplevelItemId :: String -> String
toplevelItemId item = fst $ break (\c -> c == '/' || c == '.') item

-- | Construct the identifier for an individual toplevel item.
-- The first argument is the linkage prefix for internal linkage or "" otherwise.
-- The second argument is the C identifier of the item.
individualItemId :: String -> String -> String
individualItemId pref cid = if null pref then cid else pref ++ ":" ++ cid

-- | Construct the identifier for an individual local item.
-- The argument is the C identifier of the item.
localItemId :: String -> String
localItemId cid = '?' : cid

-- | Construct the identifier for an individual parameter item.
-- The argument is the C identifier of the item.
paramItemId :: String -> String
paramItemId cid = "param|" ++ cid

-- | Construct the identifier for a collective item specified by a typedef name.
typedefItemId :: String -> String
typedefItemId cid = "typedef|" ++ cid

-- | Construct the identifier for a collective item specified by a tag name.
-- The first argument is the kind of tag (struct, union, enum).
-- The second argument is the tag name or "" for an anonymous tag.
tagItemId :: String -> String -> String
tagItemId knd "" = knd ++ "|<anonymous>"
tagItemId knd cid = knd ++ "|" ++ cid

-- | Construct the identifier for a member subitem of an item of struct or union type.
-- The first argument is the identifier of the main item.
-- The second argument is the C identifier of the member.
memberSubItemId :: String -> String -> String
memberSubItemId item cid = item ++ "." ++ cid

-- | Construct the identifier for the element subitem of an item of array type.
elemSubItemId :: String -> String
elemSubItemId item = item ++ "/[]"

-- | Construct the identifier for the referenced data subitem of an item of pointer type.
-- The '&' case handles the internal form used for adjusted funtion types (see @adjustItemAssocType@).
refSubItemId :: String -> String
refSubItemId ('&' : item) = item
refSubItemId item = item ++ "/*"

-- | Construct the identifier for the result subitem of an item of function type.
resultSubItemId :: String -> String
resultSubItemId item = item ++ "/()"

-- | Construct the identifier for a parameter subitem of an item of function type.
-- The first argument is the identifier of the main item.
-- The second argument is the parameter position (starting at 1).
-- The third argument is the C identifier of the parameter or "" if not available.
paramSubItemId :: String -> Int -> String -> String
paramSubItemId item pos cid = 
    item ++ "/" ++ (show pos) ++ pnam
    where pnam = case cid of
                      "" -> ""
                      _ -> '-' : cid

-- | Construct all identifiers for an individual item.
-- In the input parameter ids have the form <pos> or <pos>-<name>.
-- The second form is split into two separate ids using <pos> and <name>.
indivItemIds :: String -> [String]
indivItemIds iid = case elemIndex '-' iid of
                        Nothing -> [iid]
                        Just i -> sepIds i iid

sepIds i iid =
    (map (\r -> pre ++ r) seprest) ++ (map (\r -> prefix ++ name ++ r) seprest)
    where (pre,pst) = splitAt i iid -- pre is .../<pos>, pst is -<name>...
          prefix = dropWhileEnd isDigit pre -- .../
          name = takeWhile isLetter $ tail pst -- <name>
          rest = dropWhile isLetter $ tail pst -- ...
          seprest = indivItemIds rest

-- | Construct the default item identifier.
-- In the input parameter ids have the form <pos> or <pos>-<name>.
-- The default item identifier uses <name> when available, otherwise <pos>.
defaultItemId :: String -> String
defaultItemId iid = case elemIndex '-' iid of
                        Nothing -> iid
                        Just i -> defId i iid

defId i iid =
    prefix ++ name ++ defrest
    where (pre,pst) = splitAt i iid -- pre is .../<pos>, pst is -<name>...
          prefix = dropWhileEnd isDigit pre -- .../
          name = takeWhile isLetter $ tail pst -- <name>
          rest = dropWhile isLetter $ tail pst -- ...
          defrest = defaultItemId rest

-- Only temporary, used for old Parmod implementation. Transform .../<pos>-<name>... to .../<name>...
removePositions :: String -> String
removePositions iid = case elemIndex '-' iid of
                        Nothing -> iid
                        Just i -> remPos i iid

remPos i iid = prefix ++ name ++ (removePositions rest)
    where (pre,pst) = splitAt i iid -- pre is .../<pos>, pst is -<name>...
          prefix = dropWhileEnd isDigit pre -- .../
          name = takeWhile isLetter $ tail pst -- <name>
          rest = dropWhile isLetter $ tail pst -- ...

