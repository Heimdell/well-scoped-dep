
import Parser

import System.Environment
import Lexeme
import Parsing
import Pretty
import Control.Applicative
import Data.Foldable

main :: IO ()
main = do
  [fin] <- getArgs
  txt   <- readFile fin
  let lexemes = runLexer fin txt
  let lexemes' = setKW "transport Type let let-rec in refl" lexemes
  case runParser (expr <* eof) lexemes' of
    Left (rep, l) -> do
      print (pPrint (toList rep))
      print l.payload
      print (pPrint l.pos)

    Right a -> do
      print (pPrint a)