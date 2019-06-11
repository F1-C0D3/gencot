{-# LANGUAGE PackageImports #-}
module Main where

import Gencot.Input (readFromInput_)

main :: IO ()
main = do
    _ <- readFromInput_
    return ()

