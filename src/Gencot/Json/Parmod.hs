{-# LANGUAGE PackageImports, TypeSynonymInstances, FlexibleInstances #-}

-- | Define JSON function descriptions.
-- A function description is represented as a JSON object and describes a function or a function pointer. 
-- It mainly consists of a description of the function parameters. 
-- For a function definition, it additionally describes all invocations of functions
-- in the function body.
module Gencot.Json.Parmod where

import Text.JSON

type Parmod = JSObject JSValue
type Parmods = [Parmod]

-- | Read a sequence of function descriptions from stdin.
readParmodsFromInput :: IO Parmods
readParmodsFromInput = do
    inp <- getContents
    case decode inp of
         Ok res -> return res
         Error msg -> error msg

-- | Read a sequence of function descriptions from a file.
readParmodsFromFile :: FilePath -> IO Parmods
readParmodsFromFile file = do 
    inp <- readFile file 
    case decode inp of
         Ok res -> return res
         Error msg -> error msg

