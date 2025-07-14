{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
module Pass.Lexeme where

import Data.Char

import Pretty
import Pos

data LexemeType
  = BigName   String
  | SmallName String
  | KW        String
  | Integer   Integer
  | String    String
  | Punct     Char
  | Wrong     Char
  | Operator  String
  | EOF
  deriving (Eq, Ord)

instance Show LexemeType where
  show = show . pPrint

instance Pretty LexemeType where
  pPrint = \case
    BigName s -> text s
    SmallName s -> text s
    KW s -> text s
    Integer i -> integer i
    String s -> text (show s)
    Punct c -> text [c]
    Wrong c -> text [c]
    Operator s -> text s
    EOF -> "<EOF>"

data Lexeme = Lexeme
  { pos     :: Pos
  , payload :: LexemeType
  }

instance Show Lexeme where
  show = show . pPrint . (.pos)

runLexer :: FilePath -> String -> [Lexeme]
runLexer filepath source = lexing (start filepath source) source

lexing :: Pos -> String -> [Lexeme]
lexing pos [] = [Lexeme {pos, payload = EOF}]
lexing pos (c : str)
  | isAsciiUpper c
  , (cs, rest) <- span isNameBody str =
    Lexeme {pos, payload = BigName (c : cs)} : lexing (consume (c : cs) pos) rest

  | isAsciiLower c
  , (cs, rest) <- span isNameBody str =
    Lexeme {pos, payload = SmallName (c : cs)} : lexing (consume (c : cs) pos) rest

  | isDigit c
  , (cs, rest) <- span isDigit str =
    Lexeme {pos, payload = Integer (read (c : cs))} : lexing (consume (c : cs) pos) rest

  | c == '\"'
  , (cs, rest) <- break (\d -> d == '\"' || d == '\n') str =
    Lexeme {pos, payload = String (c : cs)} : lexing (consume (c : cs ++ "\"") pos) (drop 1 rest)

  | c == '#'
  , (cs, rest) <- break (== '\n') str =
    lexing (consume (c : cs) pos) rest

  | isOperator c
  , (cs, rest) <- span isOperator str =
    Lexeme {pos, payload = Operator (c : cs)} : lexing (consume (c : cs) pos) rest

  | isPunct c = Lexeme {pos, payload = Punct c} : lexing (advance c pos) str
  | isSpace c = lexing (advance c pos) str
  | otherwise = Lexeme {pos, payload = Wrong c} : lexing (advance c pos) str

isNameBody, isOperator, isPunct :: Char -> Bool
isNameBody c = isAsciiUpper c || isAsciiLower c || isDigit c || c == '-' || c == '\''
isOperator c = c `elem` ("+-:*&|~<=>/" :: String)
isPunct    c = c `elem` ("[]{}(),%;." :: String)

setKW :: String -> [Lexeme] -> [Lexeme]
setKW kws = map \case
  Lexeme {pos, payload = SmallName name}
    | name `elem` words kws -> Lexeme {pos, payload = KW name}
  other -> other