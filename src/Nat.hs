{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}

{- |
  Натуральные числа.
-}
module Nat
  ( -- * Тип
    Nat(..)

  , -- * Сложение
    type (+)

  , -- * Пучок
    NatS (..)

  , -- * Синглтон
    KnownNat (natS)
  ) where

{- |
  Натуральное число.

  Мы не используем их на уровне значений.
-}
data Nat
  = O     -- ^ ноль
  | S Nat -- ^ инкремент

{- |
  Сложение чисел на уровне типов.
-}
type family a + b where
  O   + b =        b
  S a + b = S (a + b)

{- |
  Пучок, отображающий числа с уровня типов на уровень значений.
-}
data NatS (n :: Nat) where
  NatO ::               NatS  O
  NatS :: KnownNat n => NatS (S n)

{- |
  Синглтон числа.
-}
class KnownNat (n :: Nat) where
  natS :: NatS n

instance KnownNat O where
  natS = NatO

instance KnownNat n => KnownNat (S n) where
  natS = NatS
