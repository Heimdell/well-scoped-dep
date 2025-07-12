{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}

{- |
  Реализации подстановки для `Value` и `Neutral`.
-}
module Runtime.Value.Substitution
  ( -- * Элиминаторы
    transport
  , apply
  , uncurry
  ) where

import Prelude hiding (fst, snd, uncurry)

import Nat
import Vec

import Runtime.Value
import Runtime.Substitution
import Name

instance Substitutes Value where
  subst :: KnownNat bs => Subst as bs -> Value as -> Value bs
  subst s = \case
    ValueNeutral n         -> subst s n
    ValueU                 -> ValueU
    ValuePi      n ty res  -> ValuePi    n (subst s ty) (extend s `subst` res)
    ValueSigma   n fst snd -> ValueSigma n (subst s fst) (extend s `subst` snd)
    ValueEq      a x y     -> ValueEq    (subst s a) (subst s x) (subst s y)
    ValueLam     n body    -> ValueLam   n (extend s `subst` body)
    ValuePair    fst snd   -> ValuePair  (subst s fst) (subst s snd)
    ValueRefl              -> ValueRefl

instance Substitutes Neutral where
  subst :: KnownNat bs => Subst as bs -> Neutral as -> Value bs
  subst s = \case
    NeutralVar     var           -> index var s
    NeutralApp     f x           -> apply     (subst s f) (subst s x)
    NeutralUncurry fst snd p k   -> uncurry    fst snd (subst s p) (extend (extend s) `subst` k)
    NeutralTransp  a x y p px eq -> transport (subst s a) (subst s x) (subst s y) (subst s p) (subst s px) (subst s eq)

{- |
  Элиминатор равенства.

  Принимает объект элиминации шестым аргументом.
-}
transport :: Value bs -> Value bs -> Value bs -> Value bs -> Value bs -> Value bs -> Value bs
transport a x y p px eq = case eq of
  ValueNeutral n   -> ValueNeutral (NeutralTransp a x y p px n)
  ValueRefl        -> px
  _                -> error "not an equlity"

{- |
  Элиминатор функции.

  Принимает объект элиминации первым аргументом.
-}
apply :: KnownNat bs => Value bs -> Value bs -> Value bs
apply f x = case f of
  ValueNeutral n    -> ValueNeutral (NeutralApp n x)
  ValueLam   _ body -> (x :> keep) `subst` body
  _                 -> error "not an function"

{- |
  Элиминатор пары.

  Принимает объект элиминации третьим аргументом.
-}
uncurry :: KnownNat bs => Name -> Name -> Value bs -> Value (S (S bs)) -> Value bs
uncurry fst snd pair k = case pair of
  ValueNeutral n      -> ValueNeutral (NeutralUncurry fst snd n k)
  ValuePair fst' snd' -> (snd' :> fst' :> keep) `subst` k
  _                   -> error "not a pair"
