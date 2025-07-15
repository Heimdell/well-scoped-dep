
module Data.Name where

import Data.Function (on)
import Text.Pos
import Data.String

data Name = Name
  { pos :: Pos
  , raw :: String
  }

instance Eq  Name where (==)    = (==)    `on` (.raw)
instance Ord Name where compare = compare `on` (.raw)

instance IsString Name where
  fromString raw = Name {raw, pos = start "" ""}

newtype LocatedName = LocatedName {name :: Name}

newtype Name' = Name' {name :: Name}

instance Eq  Name' where (==)    _ _ = True
instance Ord Name' where compare _ _ = EQ
