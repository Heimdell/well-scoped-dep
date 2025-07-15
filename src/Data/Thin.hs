{- |
  Разбавление контекстов, оно же отношение подпоследовательности над контекстами.

  Контексты можно представить как списки, содержащие информацию обо всех
  свободных переменных в терме. Так как эта информация равномощна 1, мы
  можем вместо списка использовать его длину (@List () ~ Nat@).

  Т.е., контекст - это количество связанных переменных в терме.
-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Data.Thin
  ( -- * Типы
    type (<=) (..)
  , Below
  , -- * Смарт-конструкторы
    none
  , every
  , weaken
  , splitVar
  , -- * Композиция
    o
  , -- * Функтор
    Thinning (thin)
  ) where

import Data.Nat

{- |
  Доказательство того, что @m@ это разбавленный контекст @n@.

  Можно представить как битовую маску длины @m@ в которой есть @n@ единиц.

  Конструктор `Empty` соответствует пустой маске.

  Конструктор `Drop` сообветствует присоединению бита @0@ к маске слева.

  Конструктор `Keep` сообветствует присоединению бита @1@ к маске слева.
-}
data (<=) n m where
  Empty ::           O   <= O    -- ^ Пустой контекст разбавляется себя
  Drop  :: n <= m ->   n <= S m  -- ^ Добавление переменной
  Keep  :: n <= m -> S n <= S m  -- ^ Перенос переменной

instance Eq (n <= m) where
  a == b = case (a, b) of
    (Empty,  Empty)  -> True
    (Drop n, Drop m) -> n == m
    (Keep n, Keep m) -> n == m
    _                -> False

{- |
  Композиция разбавлений.
-}
o :: n <= m -> m <= o -> n <= o
Empty   `o` Empty   = Empty
nm      `o` Drop mo = Drop (nm `o` mo)
Drop nm `o` Keep mo = Drop (nm `o` mo)
Keep nm `o` Keep mo = Keep (nm `o` mo)

{- |
  Подтип масок, в которых ровно 1 единица.

  Проще говоря, выборка ровно 1 элемента из контекста длины @m@.

  Ну, или ссылка на этот элемент.
-}
type Below m = S O <= m

{- |
  Пустая выборка из контекста, все нули.
-}
none :: forall n. KnownNat n => O <= n
none = case natS @n of
  NatO -> Empty
  NatS -> Drop none

{- |
  Полная выборка из контекста, все единицы.
-}
every :: forall n. KnownNat n => n <= n
every = case natS @n of
  NatO -> Empty
  NatS -> Keep every

weaken ::
     forall d n m
  .  KnownNat d
  => n <=      m
  -> n <= (d + m)
weaken th = case natS @d of
  NatO     -> th
  NatS @d1 -> Drop (weaken @d1 th)

{- |
  "Разбавляемость" конструкции @p@.

  Позволяет заменить контекст @as@ у @p as@ на разбавленный @bs@, при
  предоставлении доказателства, что @as@ разбавляет @bs@ - @as <= bs@.
-}
class Thinning p where
  thin :: as <= bs -> p as -> p bs

splitVar ::
     forall d n
  .  KnownNat d
  => Below        (d +       n)
  -> Either (Below d) (Below n)
splitVar var = case natS @d of
  NatO -> pure var
  NatS @d1 -> case var of
    Keep _   -> Left (Keep none)
    Drop var' -> case splitVar @d1 @n var' of
      Left  used -> Left (Drop used)
      Right rest -> Right rest
