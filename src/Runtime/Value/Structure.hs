{-# LANGUAGE NoFieldSelectors #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE DataKinds #-}

{- |
  Нормальная форма NbE-вычислителя.
-}
module Runtime.Value.Structure
  ( -- * Типы
    Value (..)
  , Neutral (..)
  ) where

import Nat
import Thin
import Name

{- |
  Вычисленное значение.

  Все конструкторы, кроме `ValueNeutral` соответствуют "конструкторам"
  (в типо-теоретическом смысле) из типа `Expr`.
-}
data Value (n :: Nat)
  = -- | Вычисленное выражение может быть застрявшим
    ValueNeutral { neutral :: Neutral n }

  | ValueU
  | ValuePi      { argName :: Name, argTy :: Value n, resTy :: Value (S n) }
  | ValueSigma   { fstName :: Name, fstTy :: Value n, sndTy :: Value (S n) }
  | ValueEq      { x, y :: Value n }

  | ValueLam     { argName :: Name, body :: Value (S n) }
  | ValuePair    { fst, snd :: Value n }
  | ValueRefl

{- |
  "Застрявшее" значение.

  Конструкторы это либо свободная переменная, либо элиминатор, застрявший в главном
  аргкиенте.
-}
data Neutral (n :: Nat)
  = NeutralVar     { var :: Below n }
  | NeutralApp     { f :: Neutral n, x :: Value n }
  | NeutralUncurry { fstName, sndName :: Name, pair :: Neutral n, consume :: Value (S (S n)) }
  | NeutralTransp  { a, x, y, p, px :: Value n, eq :: Neutral n }
