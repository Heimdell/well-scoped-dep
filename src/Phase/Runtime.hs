module Phase.Runtime
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

import Phase.Runtime.Value (Value (..), Neutral(..))
import Phase.Runtime.Value.Thinning ()
import Phase.Runtime.Value.Substitution (transport, apply, uncurry)
import Phase.Runtime.Substitution
  ( Subst
    , keep
    , extend
    , Substitutes (subst)
    )