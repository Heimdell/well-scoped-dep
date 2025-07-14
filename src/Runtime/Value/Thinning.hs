{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BlockArguments #-}

{- |
  Реализации разбавления для `Value` и `Neutral`.
-}
module Runtime.Value.Thinning () where

import Prelude hiding (fst, snd, uncurry)

import Runtime.Value.Structure
import Thin

instance Thinning Value where
  thin :: as <= bs -> Value as -> Value bs
  thin th = \case
    ValueNeutral n         -> ValueNeutral (thin th n)
    ValueU                 -> ValueU
    ValuePi      n ty res  -> ValuePi       n (thin th ty) (thin (Keep th) res)
    ValueSigma   n fst snd -> ValueSigma    n (thin th fst) (thin (Keep th) snd)
    ValueEq          x y   -> ValueEq      (thin th x) (thin th y)
    ValueLam     n body    -> ValueLam      n (thin (Keep th) body)
    ValuePair    fst snd   -> ValuePair     (thin th fst) (thin th snd)
    ValueRefl              -> ValueRefl

instance Thinning Neutral where
  thin :: as <= bs -> Neutral as -> Neutral bs
  thin th = \case
    NeutralVar     var           -> NeutralVar     (var `o` th)
    NeutralApp     f x           -> NeutralApp     (thin th f) (thin th x)
    NeutralUncurry fst snd p k   -> NeutralUncurry  fst snd (thin th p) (thin (Keep (Keep th)) k)
    NeutralTransp  a x y p px eq -> NeutralTransp  (thin th a) (thin th x) (thin th y) (thin th p) (thin th px) (thin th eq)
