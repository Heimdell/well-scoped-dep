
import Data.Foldable
import Data.Vec
import Data.Nat
import System.Environment
import Text.Parsing
import Text.Pretty

import Pass.Lexeme
import Pass.Parser
import Pass.Scoping as Scoping
import Pass.Typing as Typing
import Pass.Eval
import Phase.Scoped ()
import Control.Monad.Except (runExceptT)
import Control.Monad.Writer

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
      case Scoping.check Nil a of
        Left err -> print (pPrint err)
        Right a' -> do
          case runWriter $ runExceptT $ Typing.infer Nil Nil a' of
            (Left (err, scope, pos), warn) -> do
              print (pPrint err)
              print (pPrint pos)
              print (vcat ["Scope:", nest 2scope])
              putStrLn ""
              for_ warn (print . pPrint)

            (Right a'', warn) -> do
              print (pic Nil (eval NatO a'))
              putStrLn ":"
              print (pic Nil a'')
              putStrLn ""
              for_ warn (print . pPrint)
