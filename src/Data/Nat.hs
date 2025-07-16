{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}

{- |
  Натуральные числа.
-}
module Data.Nat
  ( -- * Тип
    Nat(..)

  , -- * Сложение
    type (+)

  , -- * Пучок
    NatS (..)

  , add

  -- , -- * Синглтон
  --   KnownNat (natS)
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
  NatO ::           NatS  O
  NatS :: NatS n -> NatS (S n)

add :: NatS d -> NatS n -> NatS (d + n)
add = \case
  NatO   -> id
  NatS d -> NatS . add d

-- {- |
--   Синглтон числа.
-- -}
-- class KnownNat (n :: Nat) where
--   natS :: NatS n

-- instance KnownNat O where
--   natS = NatO

-- instance KnownNat n => KnownNat (S n) where
--   natS = NatS
