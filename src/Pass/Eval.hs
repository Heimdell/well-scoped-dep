{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BlockArguments #-}

{- |
  Приведение выражения к нормальной форме.
-}

module Pass.Eval (eval) where

import Prelude hiding (fst, snd, uncurry)

import Phase.Runtime
import Nat
import Vec
import Phase.Scoped

{- |
  Переаод выражения в нормальную форму.
-}
eval :: KnownNat n => Expr n -> Value n
eval = \case
  ExprVar var -> ValueNeutral (NeutralVar var)

  ExprU                   -> ValueU
  ExprPi      n arg res   -> ValuePi      n (eval arg) (eval res)
  ExprSigma   n fst snd   -> ValueSigma   n (eval fst) (eval snd)
  ExprEq        x y       -> ValueEq      (eval x) (eval y)
  ExprLam     n body      -> ValueLam     n (eval body)
  ExprPair    fst snd     -> ValuePair    (eval fst) (eval snd)
  ExprRefl                -> ValueRefl

  ExprApp     f x           -> apply     (eval f) (eval x)
  ExprUncurry fst snd p k   -> uncurry    fst snd (eval p) (eval k)
  ExprTransp  a x y p px eq -> transport (eval a) (eval x) (eval y) (eval p) (eval px) (eval eq)

  ExprLetRec  decls rest -> do
    let
      decls' = fmap (\(_name, _ty, val) -> subst sub (eval val)) decls
      sub = decls' +++ keep

    subst sub (eval rest)
