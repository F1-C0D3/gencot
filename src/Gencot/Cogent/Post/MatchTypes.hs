{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Post.MatchTypes where

import Data.List (concatMap,nub,intersect,union,(\\),partition,find)
import qualified Data.Map as M
import Data.Maybe (catMaybes,isNothing,fromJust)
import Data.Foldable (toList)

import Cogent.Surface as CS
import Cogent.Common.Syntax as CCS

import Gencot.Cogent.Ast

{- Matching readonly subexpressions -}
{- to linear context: always error  -}
{------------------------------------}

roproc :: GenExpr -> GenExpr
roproc e = e

{- Matching linear subexpressions -}
{- to readonly context: try bang  -}
{----------------------------------}

bangproc :: GenExpr -> GenExpr
bangproc e = e
