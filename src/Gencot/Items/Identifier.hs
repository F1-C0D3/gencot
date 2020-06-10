{-# LANGUAGE PackageImports #-}
module Gencot.Items.Identifier where

import Data.Char (isDigit,isLetter,isAlphaNum)
import Data.List (break,elemIndex,dropWhileEnd,any,find,findIndices,isSuffixOf,isPrefixOf)

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
-- The second argument is the tag name or a pseudo tag name for an anonymous tag.
tagItemId :: String -> String -> String
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

-- | Test an item id whether it is a toplevel object or function id.
-- It is tested whether it contains no slash, dot, or bar.
isToplevelObjectId :: String -> Bool
isToplevelObjectId item = all (\c -> c /= '/' && c /= '.' && c /= '|') item

-- | Test an item id whether it is a parameter id built using @paramSubItemId@.
-- It is tested whether the last slash is followed by a digit and there is no dot after it.
isParameterId :: String -> Bool
isParameterId item = 
    if null sis 
       then False
       else let li = last sis
            in if (li + 1) == length item 
                  then False
                  else if any (\di -> di > li) dis
                          then False
                          else isDigit $ item !! (li + 1)
    where sis = findIndices (== '/') item
          dis = findIndices (== '.') item

-- | Test an item id whether it is embedded in a composite type or array.
-- It is tested whether it contains a dot with no slash or colon after it (composite type member)
-- (a colon ends a file name used as prefix for items with internal linkage)
-- or it ends with "/[]" (array element)
isEmbeddedId :: String -> Bool
isEmbeddedId item =
    if "/[]" `isSuffixOf` item 
       then True
       else if null dis 
                then False
                else if null sis
                        then True
                        else (last dis) > (last sis)
    where sis = findIndices (\c -> c == '/' || c == ':') item
          dis = findIndices (== '.') item

-- | Construct all identifiers for an individual item.
-- In the input parameter ids have the form <pos> or <pos>-<name>.
-- The second form is split into two separate ids using <pos> and <name>.
indivItemIds :: String -> [String]
indivItemIds iid = case firstDashAfterColonIndex iid of
                        Nothing -> [iid]
                        Just i -> sepIds i iid

-- | Index of the first '-' after the last colon ':'.
firstDashAfterColonIndex :: String -> Maybe Int
firstDashAfterColonIndex iid =
    if null dis then Nothing
                else if null cis then Just $ head dis
                                 else find (\i -> i > last cis) dis
    where cis = findIndices (== ':') iid
          dis = findIndices (== '-') iid

sepIds i iid =
    (map (\r -> pre ++ r) seprest) ++ (map (\r -> prefix ++ name ++ r) seprest)
    where (pre,pst) = splitAt i iid -- pre is .../<pos>, pst is -<name>...
          prefix = dropWhileEnd isDigit pre -- .../
          name = takeWhile isAlphaNum $ tail pst -- <name>
          rest = dropWhile isAlphaNum $ tail pst -- ...
          seprest = indivItemIds rest

-- | Construct the default item identifier.
-- In the input parameter ids have the form <pos> or <pos>-<name>.
-- The default item identifier uses <name> when available, otherwise <pos>.
defaultItemId :: String -> String
defaultItemId iid = case firstDashAfterColonIndex iid of
                        Nothing -> iid
                        Just i -> defId i iid

defId i iid =
    prefix ++ name ++ defrest
    where (pre,pst) = splitAt i iid -- pre is .../<pos>, pst is -<name>...
          prefix = dropWhileEnd isDigit pre -- .../
          name = takeWhile isAlphaNum $ tail pst -- <name>
          rest = dropWhile isAlphaNum $ tail pst -- ...
          defrest = defaultItemId rest

-- | Retrieve all typedef names from a list of toplevel item identifiers.
getTypedefNames :: [String] -> [String]
getTypedefNames [] = []
getTypedefNames (iid : rest) = 
    if "typedef|" `isPrefixOf` iid 
       then (drop 8 iid) : (getTypedefNames rest)
       else getTypedefNames rest

-- | Retrieve an object or function name from a toplevel item identifier.
-- For items with internal linkage the prefix must be removed.
getObjFunName :: String -> String
getObjFunName iid =
    if null pst then iid else tail pst
    where (pre,pst) = break (== ':') iid
