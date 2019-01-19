module Main where
import System.Environment
import System.FilePath
import System.Exit
import System.IO
import Control.Arrow      hiding ((<+>))
import Control.Monad
import Debug.Trace
import Text.PrettyPrint.HughesPJ
import Data.List

import Language.C              -- simple API
import Language.C.Analysis     -- analysis API
import Language.C.Analysis.Debug -- debugging printer for analysis
import Language.C.System.GCC   -- preprocessor used

usageMsg :: String -> String
usageMsg prg = render $ text "Usage:" <+> text prg <+> hsep (map text ["CPP_OPTIONS","input_file.c"])

main :: IO ()
main = do
  let usageErr = (hPutStrLn stderr (usageMsg "./ParseAndPrint") >> exitWith (ExitFailure 1))
  args <- getArgs
  when (length args < 1) usageErr
  let (opts,input_file) = (init args, last args)
  ast <- errorOnLeftM "Parse Error" $ parseCFile (newGCC "gcc") Nothing opts input_file

  (globals,warnings) <- errorOnLeft "Semantic Error" $ runTrav_ $ analyseAST ast

  mapM (hPutStrLn stderr . show) warnings
  print $ pretty $ filterGlobalDecls (maybe False (fileOfInterest pat input_file) . fileOfNode) globals

  where
  pat = Nothing
  fileOfInterest (Just pat) _ file_name = pat `isInfixOf` file_name
  fileOfInterest Nothing input_file file_name = fileOfInterest' (splitExtensions input_file) (splitExtension file_name)
  fileOfInterest' (c_base,c_ext) (f_base,f_ext) | takeBaseName c_base /= takeBaseName f_base = False
                                                | f_ext == ".h" && c_ext == ".c"  = False
                                                | otherwise = True

errorOnLeft :: (Show a) => String -> (Either a b) -> IO b
errorOnLeft msg = either (error . ((msg ++ ": ")++).show) return

errorOnLeftM :: (Show a) => String -> IO (Either a b) -> IO b
errorOnLeftM msg action = action >>= errorOnLeft msg

