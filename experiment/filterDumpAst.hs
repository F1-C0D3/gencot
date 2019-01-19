import Data.ByteString (getContents)

import Language.C (parseC,initPos)

main :: IO ()
main = do
  input_stream <- Data.ByteString.getContents
  ast <- either (error . show) return $ parseC input_stream (initPos "<stdin>")
  putStrLn $ (decorate (shows ast) "")

errorOnLeft :: (Show a) => String -> (Either a b) -> IO b
errorOnLeft msg = either (error . ((msg ++ ": ")++).show) return

decorate app = showString "(" . app . showString ")"
