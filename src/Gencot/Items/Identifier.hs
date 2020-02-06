{-# LANGUAGE PackageImports #-}
module Gencot.Items.Identifier where

import Data.List (break)

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

