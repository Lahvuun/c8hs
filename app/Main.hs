module Main where

import qualified Data.ByteString.Lazy as BS
import qualified MyLib
import System.IO (stdin)

main :: IO ()
main = do
  bytes <- BS.hGetContents stdin
  MyLib.run bytes
