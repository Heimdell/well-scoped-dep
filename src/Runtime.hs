module Runtime
  ( Value (..)
  , Neutral (..)
  , transport
  , apply
  , uncurry
  , Subst
  , keep
  , extend
  , Substitutes (subst)
  ) where

import Prelude hiding (uncurry)

import Runtime.Value (Value (..), Neutral(..))
import Runtime.Value.Thinning ()
import Runtime.Value.Substitution (transport, apply, uncurry)
import Runtime.Substitution
  ( Subst
    , keep
    , extend
    , Substitutes (subst)
    )