{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BlockArguments #-}

{- |
  Приведение выражения к нормальной форме.
-}

module Pass.Eval (eval) where

import Prelude hiding (fst, snd, uncurry)

import Phase.Runtime
import Data.Nat
import Data.Vec
import Phase.Scoped
import Text.Pretty (pPrint)

{- |
  Переаод выражения в нормальную форму.
-}
eval :: NatS n -> Expr n -> Value n
eval bs (_ :@ expr) = case expr of
  ExprVar var             -> ValueNeutral (NeutralVar var)

  ExprU                   -> ValueU
  ExprPi      n arg res   -> ValuePi      n (eval bs arg) (eval (NatS bs) res)
  ExprSigma   n fst snd   -> ValueSigma   n (eval bs fst) (eval (NatS bs) snd)
  ExprEq        x y       -> ValueEq      (eval bs x) (eval bs y)
  ExprLam     n body      -> ValueLam     n (eval (NatS bs) body)
  ExprPair    fst snd     -> ValuePair    (eval bs fst) (eval bs snd)
  ExprRefl                -> ValueRefl

  ExprApp     f x           -> apply     bs (eval bs f) (eval bs x)
  ExprUncurry fst snd p k   -> uncurry   bs  fst snd (eval bs p) (eval (NatS (NatS bs)) k)
  ExprTransp  a x y p px eq -> transport
    (eval bs a)
    (eval bs x)
    (eval bs y)
    (eval bs p)
    (eval bs px)
    (eval bs eq)

  ExprHole _ name -> ValueNeutral (NeutralHole name)

  ExprLetRec d _names _tys (fmap (eval (add d bs)) -> vals) rest -> do
    let
      decls' = fmap (subst bs sub) vals
      sub    = decls' +++ keep bs

    subst bs sub (eval (d `add` bs) rest)
