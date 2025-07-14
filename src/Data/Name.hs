
module Data.Name where

import Data.Pos
import Data.Function (on)

data Name = Name
  { pos :: Pos
  , raw :: String
  }

instance Eq  Name where (==)    = (==)    `on` (.raw)
instance Ord Name where compare = compare `on` (.raw)

newtype LocatedName = LocatedName {name :: Name}
