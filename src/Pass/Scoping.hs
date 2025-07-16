{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module Pass.Scoping where

import Prelude hiding (fst, snd, uncurry, unzip)

import Control.Monad.Except
import Data.Vec
import Data.Name
import Data.Nat
import Data.Thin
import Text.Pos
import Text.Pretty

import Phase.Raw as In
import Phase.Scoped as Out
import Data.Traversable
import Data.Foldable (for_)

data Err
  = Undefined Pos Name
  | Shadowing Pos Name Pos

instance Pretty Err where
  pPrint = \case
    Undefined pos name ->
      vcat
        [ "Undefined" <+> pPrint name
        , pPrint pos
        ]
    Shadowing pos name old ->
      vcat
        [ "Shadowing of" <+> pPrint name
        , pPrint pos
        , ""
        , "Originating from"
        , pPrint old
        ]

find :: forall n. Name -> Vec n Name -> Either Err (Below n)
find name env = case env of
  Nil -> throwError (Undefined name.pos name)
  n :> env'
    | n == name -> pure (Keep (none (len env')))
    | otherwise -> Drop <$> find name env'

findNot :: Name -> Vec n Name -> Either Err ()
findNot name = \case
  Nil -> pure ()
  n :> env'
    | n == name -> throwError (Shadowing name.pos name n.pos)
    | otherwise -> findNot name env'

check :: Vec n Name -> In.Expr -> Either Err (Out.Expr n)
check env = \case
  In.ExprVar name -> Out.ExprVar <$> find name env

  In.ExprU -> pure Out.ExprU

  In.ExprPi arg ty res -> do
    findNot arg env
    Out.ExprPi arg
      <$> check         env  ty
      <*> check (arg :> env) res

  In.ExprSigma arg ty res -> do
    findNot arg env
    Out.ExprSigma arg
      <$> check         env  ty
      <*> check (arg :> env) res

  In.ExprEq x y -> do
    Out.ExprEq
      <$> check env x
      <*> check env y

  In.ExprLam arg body -> do
    findNot arg env
    Out.ExprLam arg
      <$> check (arg :> env) body

  In.ExprPair fst snd -> do
    Out.ExprPair
      <$> check env fst
      <*> check env snd

  In.ExprRefl -> pure Out.ExprRefl

  In.ExprApp f x -> do
    Out.ExprApp
      <$> check env f
      <*> check env x

  In.ExprUncurry fst snd pair uncurry -> do
    findNot fst env
    findNot snd env
    Out.ExprUncurry fst snd
      <$> check env pair
      <*> check (snd :> fst :> env) uncurry

  In.ExprTransp a x y p px eq -> do
    Out.ExprTransp
      <$> check env a
      <*> check env x
      <*> check env y
      <*> check env p
      <*> check env px
      <*> check env eq

  In.ExprHole name -> pure (Out.ExprHole name)

  In.ExprLetRec decls k -> do
    for_ decls \(n, _, _) -> do
      findNot n env

    delta <- deltaEnv env decls
    case delta of
      Delta dEnv decls' -> do
        (tys, vals) <- unzip <$> for decls' (checkDecl dEnv env)
        Out.ExprLetRec (len dEnv) dEnv tys vals
          <$> check (dEnv +++ env) k

checkDecl ::
     Vec d Name
  -> Vec n Name
  -> (Name, In.Expr, In.Expr)
  -> Either Err (Out.Expr n, Out.Expr (d + n))
checkDecl dEnv env (_, ty, val) = do
  (,)
    <$> check env ty
    <*> check (dEnv +++ env) val

deltaEnv ::
     Vec n Name
  -> [(Name, In.Expr, In.Expr)]
  -> Either Err (Delta n)
deltaEnv env = \case
  [] -> do
    pure (Delta Nil Nil)

  d@(n, _, _) : ds -> do
    Delta {delta, decls} <- deltaEnv env ds
    pure $ Delta (n :> delta) (d :> decls)

data Delta n
  = forall d
  . Delta
      { delta :: Vec d Name
      , decls :: Vec d (Name, In.Expr, In.Expr)
      }