{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}

{- |
  Реализации подстановки для `Value` и `Neutral`.
-}
module Phase.Runtime.Value.Substitution
  ( -- * Элиминаторы
    transport
  , apply
  , uncurry
  ) where

import Prelude hiding (fst, snd, uncurry)

import Data.Nat
import Data.Vec
import Data.Name

import Phase.Runtime.Value.Structure
import Phase.Runtime.Substitution

instance Substitutes Value where
  subst :: NatS bs -> Subst as bs -> Value as -> Value bs
  subst bs s = \case
    ValueNeutral n         -> subst bs s n
    ValueU                 -> ValueU
    ValuePi      n ty res  -> ValuePi    n (subst bs s ty)  (subst (NatS bs) (extend bs s) res)
    ValueSigma   n fst snd -> ValueSigma n (subst bs s fst) (subst (NatS bs) (extend bs s) snd)
    ValueEq        x y     -> ValueEq    (subst bs s x) (subst bs s y)
    ValueLam     n body    -> ValueLam   n (subst (NatS bs) (extend bs s) body)
    ValuePair    fst snd   -> ValuePair  (subst bs s fst) (subst bs s snd)
    ValueRefl              -> ValueRefl

instance Substitutes Neutral where
  subst :: NatS bs -> Subst as bs -> Neutral as -> Value bs
  subst bs s = \case
    NeutralVar     var           -> index var s
    NeutralApp     f x           -> apply     bs (subst bs s f) (subst bs s x)
    NeutralUncurry fst snd p k   -> uncurry   bs  fst snd (subst bs s p) (subst (NatS (NatS bs)) (extend (NatS bs) (extend bs s)) k)
    NeutralTransp  a x y p px eq -> transport
      (subst bs s a)
      (subst bs s x)
      (subst bs s y)
      (subst bs s p)
      (subst bs s px)
      (subst bs s eq)

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
apply :: NatS bs -> Value bs -> Value bs -> Value bs
apply bs f x = case f of
  ValueNeutral n    -> ValueNeutral (NeutralApp n x)
  ValueLam   _ body -> subst bs (x :> keep bs) body
  _                 -> error "not an function"

{- |
  Элиминатор пары.

  Принимает объект элиминации третьим аргументом.
-}
uncurry :: NatS bs -> Name -> Name -> Value bs -> Value (S (S bs)) -> Value bs
uncurry bs fst snd pair k = case pair of
  ValueNeutral n      -> ValueNeutral (NeutralUncurry fst snd n k)
  ValuePair fst' snd' -> subst bs (snd' :> fst' :> keep bs) k
  _                   -> error "not a pair"
