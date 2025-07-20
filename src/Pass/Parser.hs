module Pass.Parser where

import Prelude hiding (pi, uncurry)

import Control.Applicative
import Data.Name
import Pass.Lexeme
import Data.String
import Text.Parsing

import Phase.Raw
import Text.Pos

type P = Parser LexemeType Lexeme

name :: P Name
name = do
  match (BigName "name") \case
    Lexeme {payload = BigName   raw, pos} -> pure Name {pos, raw}
    Lexeme {payload = SmallName raw, pos} -> pure Name {pos, raw}
    _                                     -> Nothing

instance (a ~ ()) => IsString (P a) where
  fromString str = do
    -- traceShowM ("match", str)
    match (KW str) \case
      Lexeme {payload = pld} | str == show pld -> Just ()
      _                                        -> Nothing

eof :: P ()
eof = match EOF \case
  Lexeme {payload = EOF} -> Just ()
  _                      -> Nothing

ctor :: P (Pos -> a) -> P a
ctor mc = mc <*> project (.pos)

term, expr :: P Expr
term = do
  p <- project (.pos)
  asum
    [ (p :@) . ExprVar <$> name
    ,  p :@    ExprU   <$ "Type"

    , pi
    , sigma

    ,      lam
    ,      pair
    , p :@ ExprRefl  <$ "refl"

    , uncurry

    , transport

    , (p :@) . ExprHole False <$ "?" <*> name

    , letrec
    ]

position :: P Pos
position = project (.pos)

pair, app :: P Expr
pair = foldl (\l (p, r) -> p :@ ExprPair l r) <$ "(" <*> expr <*> many ((,) <$> position <* ","  <*> expr) <* ")"
expr = foldl (\x (p, y) -> p :@ ExprEq   x y)        <$> app  <*> many ((,) <$> position <* "==" <*> app)
app  = foldl (\f (p, x) -> p :@ ExprApp  f x)        <$> term <*> many ((,) <$> position         <*> term)

pi :: P Expr
pi = collect <$ "[" <*> ((,) <$> position <*> arg) `sepBy1` "," <* "]" <* "->" <*> expr
  where
    collect = flip (foldr \(pos, (arg', ty)) res -> pos :@ ExprPi arg' ty res)

    arg :: P (Name, Expr)
    arg = (,) <$> name <* ":" <*> expr

sigma :: P Expr
sigma = collect <$
  "{" <*> ((,) <$> position <*> field) `sepBy1` "," <* "|" <*> expr <* "}"
  where
    collect = flip (foldr \(pos, (arg', ty)) res -> pos :@ ExprSigma arg' ty res)

    field :: P (Name, Expr)
    field = (,) <$> name <* ":" <*> expr

lam :: P Expr
lam = flip (foldr (\(p, arg) body -> p :@ ExprLam arg body))
  <$ "\\" <*> ((,) <$> position <*> name) `sepBy1` "," <* "->" <*> expr

uncurry :: P Expr
uncurry = (\p a b c d -> p :@ ExprUncurry a b c d )
  <$> position
  <* "let" <*> name <* "," <*> name <* "=" <*> expr
  <* "in" <*> expr

transport :: P Expr
transport = (\p a b c d e f -> p :@ ExprTransp a b c d e f)
  <$> position
  <* "transport" <* "("
    <*> expr <* ","
    <*> expr <* ","
    <*> expr <* ","
    <*> expr <* ","
    <*> expr <* ","
    <*> expr
  <* ")"

letrec :: P Expr
letrec = (\p decls k -> p :@ ExprLetRec decls k)
  <$> position
  <*  "let-rec" <*> (decl `sepBy` ";")
  <*  "in"      <*> expr

decl :: P (Name, Expr, Expr)
decl = (,,) <$> name <* ":" <*> expr <* "=" <*> expr