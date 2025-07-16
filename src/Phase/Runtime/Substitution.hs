{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

{- |
  Подстановка.
-}
module Phase.Runtime.Substitution
  ( -- * Подстановка
    Subst
  , keep
  , extend
  , -- * "Функтор"
    Substitutes (subst)
  ) where

import Data.Vec
import Data.Nat
import Data.Thin
import Phase.Runtime.Value.Structure
import Phase.Runtime.Value.Thinning ()

{- |
  Подстановка из контекста @from@ в контекст @to@ представляет себя по одному
  значению в контексте @to@ для каждого элемента контекста @from@.
-}
type Subst from to = Vec from (Value to)

{- |
  Расширить подстановку на один нейтральный элемент.
-}
extend :: NatS bs -> Subst as bs -> Subst (S as) (S bs)
extend bs sub
  = ValueNeutral (NeutralVar (Keep (none bs)))
  :> fmap (thin (Drop (every bs))) sub

{- |
  Юнит-подстановка.

  Не меняет объект, к которому применена.
-}
keep :: NatS as -> Subst as as
keep = \case
  NatO   -> Nil
  NatS n -> extend n (keep n)

{- |
  Подстановка позволяет отобразить структуру @p@ во входном контексте @as@
  в значение в выходном контексте @bs@.
-}
class Substitutes p where
  subst :: NatS bs -> Subst as bs -> p as -> Value bs