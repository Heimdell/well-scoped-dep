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

import Vec
import Phase.Runtime.Value.Structure
import Nat
import Thin
import Phase.Runtime.Value.Thinning ()

{- |
  Подстановка из контекста @from@ в контекст @to@ представляет себя по одному
  значению в контексте @to@ для каждого элемента контекста @from@.
-}
type Subst from to = Vec from (Value to)

{- |
  Расширить подстановку на один нейтральный элемент.
-}
extend :: KnownNat bs => Subst as bs -> Subst (S as) (S bs)
extend sub
  = ValueNeutral (NeutralVar (Keep none))
  :> fmap (thin (Drop every)) sub

{- |
  Юнит-подстановка.

  Не меняет объект, к которому применена.
-}
keep :: forall as. KnownNat as => Subst as as
keep = case natS @as of
  NatO -> Nil
  NatS -> extend keep

{- |
  Подстановка позволяет отобразить структуру @p@ во входном контексте @as@
  в значение в выходном контексте @bs@.
-}
class Substitutes p where
  subst :: KnownNat bs => Subst as bs -> p as -> Value bs