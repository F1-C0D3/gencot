module Main where

import System.Environment (getArgs)
import Control.Monad (when,liftM)

import Gencot.Text.CTypInfo (readStructsFromFile,readFuntypsFromFile)
import Gencot.Text.Genops (procGenops)

main :: IO ()
main = do
    {- get command line arguments -}
    args <- getArgs
    when (length args /= 2)
        $ error "expected arguments: <struct types file name> <function types file name>"
    {- read type information from files -}
    structs <- readStructsFromFile (head args)
    funtyps <- readFuntypsFromFile (head (tail args))
    {- process from input to output -}
    inp <- getContents
    putStrLn $ procGenops structs funtyps inp
 
