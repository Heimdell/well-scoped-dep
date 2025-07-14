module Pass.Parser where

import Prelude hiding (pi, uncurry)

import Phase.Raw
import Parsing
import Name
import Pass.Lexeme
import Data.String
import Control.Applicative

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

term, expr :: P Expr
term = asum
  [       ExprVar   <$> name

  ,       ExprU     <$ "Type"

  ,       pi
  ,       lam
       -- app

  ,       sigma
  , foldl ExprPair  <$ "(" <*> expr <*> many ("," *> expr) <* ")"
  ,       uncurry

       -- ew
  ,       ExprRefl  <$ "refl"
  ,       transport

  ,       letrec
  ]

expr = foldl ExprEq <$> app <*> many ("==" *> app)

app :: P Expr
app = foldl1 ExprApp <$> some term

pi :: P Expr
pi = collect <$ "[" <*> arg `sepBy1` "," <* "]" <* "->" <*> expr
  where
    collect = flip (foldr \(arg', ty) res -> ExprPi arg' ty res)

    arg :: P (Name, Expr)
    arg = (,) <$> name <* ":" <*> expr

sigma :: P Expr
sigma = collect <$
  "{" <*> field `sepBy1` "," <* "|" <*> expr <* "}"
  where
    collect = flip (foldr \(arg', ty) res -> ExprSigma arg' ty res)

    field :: P (Name, Expr)
    field = (,) <$> name <* ":" <*> expr

lam :: P Expr
lam = flip (foldr ExprLam)
  <$ "\\" <*> name `sepBy1` "," <* "->" <*> expr

uncurry :: P Expr
uncurry = ExprUncurry
  <$ "let" <*> name <* "," <*> name <* "=" <*> expr
  <* "in" <*> expr

transport :: P Expr
transport = ExprTransp
  <$ "transport" <* "("
    <*> expr <* ","
    <*> expr <* ","
    <*> expr <* ","
    <*> expr <* ","
    <*> expr <* ","
    <*> expr
  <* ")"

letrec :: P Expr
letrec = ExprLetRec
  <$ "let-rec"
    <*> (decl `sepBy` ";")
  <* "in" <*> expr

decl :: P (Name, Expr, Expr)
decl = (,,) <$> name <* ":" <*> expr <* "=" <*> expr