module Pos where

import Data.Function (on)
import Control.Arrow

data Pos = Pos
  { line, col :: Int
  , filename, source :: String
  }

instance Eq Pos where
  (==) = (==) `on` ((.line) &&& (.col))

start :: FilePath -> String -> Pos
start filename source = Pos {filename, source, line = 1, col = 1}

consume :: [Char] -> Pos -> Pos
consume cs pos = foldr advance pos cs

advance :: Char -> Pos -> Pos
advance '\n' pos = pos {line = pos.line + 1, col = 1}
advance  _   pos = pos {col = pos.col + 1}
