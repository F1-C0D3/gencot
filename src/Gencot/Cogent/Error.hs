{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Error where

import Language.C.Data.Error
import Language.C.Data.Node
import Language.C.Data.Position

mkWarnInfo :: String -> Position -> ErrorInfo
mkWarnInfo msg pos = ErrorInfo LevelWarn pos (lines msg)

-- | UnSupportedError is caused by a C language construct for which processing is not (yet) supported.
newtype UnSupportedError = UnSupported ErrorInfo

instance Error UnSupportedError where
    errorInfo (UnSupported ei) = ei

instance Show UnSupportedError where show = showError "Unsupported C feature"

unSupported :: (Pos a) => a -> String -> UnSupportedError
unSupported posSrc msg = UnSupported (mkWarnInfo msg (posOf posSrc))

-- | NoParamError is caused by a missing function parameter
newtype NoParamError = NoParam ErrorInfo

instance Error NoParamError where
    errorInfo (NoParam ei) = ei

instance Show NoParamError where show = showError "Missing function parameter"

noParam :: (Pos a) => a -> String -> NoParamError
noParam posSrc msg = NoParam (mkWarnInfo msg (posOf posSrc))

-- | TypeMatchError is caused by a type differences
newtype TypeMatchError = TypeMatch ErrorInfo

instance Error TypeMatchError where
    errorInfo (TypeMatch ei) = ei

instance Show TypeMatchError where show = showError "Type mismatch"

typeMatch :: (Pos a) => a -> String -> TypeMatchError
typeMatch posSrc msg = TypeMatch (mkWarnInfo msg (posOf posSrc))

-- | TakeOpError is caused by a type differences
newtype TakeOpError = TakeOp ErrorInfo

instance Error TakeOpError where
    errorInfo (TakeOp ei) = ei

instance Show TakeOpError where show = showError "Illegal take operation"

takeOp :: (Pos a) => a -> String -> TakeOpError
takeOp posSrc msg = TakeOp (mkWarnInfo msg (posOf posSrc))

