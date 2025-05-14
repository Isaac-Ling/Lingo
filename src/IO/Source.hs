module IO.Source where

import Core.Error

import Control.Exception (catch, IOException)
import Data.ByteString.Lazy.Char8 (ByteString, unpack)
import qualified Data.ByteString.Lazy.Char8 as BS

readSource :: FilePath -> IO (CanError ByteString)
readSource f = catch (Result <$> BS.readFile f) handler
  where
    handler :: IOException -> IO (CanError ByteString)
    handler _ = return $ Error FailedToReadSourceFile Nothing
