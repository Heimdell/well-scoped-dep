
import Control.Applicative
import Data.Foldable
import System.Environment
import Text.Parsing
import Text.Pretty

import Pass.Lexeme
import Pass.Parser

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