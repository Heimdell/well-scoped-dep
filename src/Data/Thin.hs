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
  , weakenr
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
none :: NatS n -> O <= n
none n = case n of
  NatO    -> Empty
  NatS n1 -> Drop (none n1)

{- |
  Полная выборка из контекста, все единицы.
-}
every :: NatS n -> n <= n
every n = case n of
  NatO    -> Empty
  NatS n1 -> Keep (every n1)

weaken ::
     NatS d
  -> n <=      m
  -> n <= (d + m)
weaken d th = case d of
  NatO    -> th
  NatS d1 -> Drop (weaken d1 th)

weakenr ::
     forall d n m
  .  NatS d
  -> n <=  m
  -> n <= (m + d)
weakenr d = \case
  Keep th -> Keep (weakenr d th)
  Drop th -> Drop (weakenr d th)
  Empty   -> none d

{- |
  "Разбавляемость" конструкции @p@.

  Позволяет заменить контекст @as@ у @p as@ на разбавленный @bs@, при
  предоставлении доказателства, что @as@ разбавляет @bs@ - @as <= bs@.
-}
class Thinning p where
  thin :: as <= bs -> p as -> p bs

splitVar ::
     forall d n
  .  NatS d
  -> Below        (d +       n)
  -> Either (Below d) (Below n)
splitVar d var = case d of
  NatO -> pure var
  NatS d1 -> case var of
    Keep _   -> Left (Keep (none d1))
    Drop var' -> case splitVar d1 var' of
      Left  used -> Left (Drop used)
      Right rest -> Right rest
