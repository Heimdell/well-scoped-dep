{- |
  Вектор определённой длины.
-}
module Data.Vec
  ( -- * Тип
    Vec(..)
  , -- * Индексирование
    index
  , -- * Конкатенация
    (+++)
  ) where

import Data.Nat
import Data.Thin

{- |
  Вектор из элементов @a@ длины @n@.
-}
data Vec n a where
  Nil  ::                 Vec  O    a  -- ^ пустой вектор
  (:>) :: a -> Vec n a -> Vec (S n) a  -- ^ присоедниение элемента

infixr 1 :>

{- |
  Извлечение элемента вектора.

  Поскольку индекс строго меньше длины вектора, мы можем гарантировать наличие
  элемента с данным индексом.
-}
index :: Below n -> Vec n a -> a
index (Keep _) (x :> _)  = x
index (Drop i) (_ :> xs) = index i xs

{- |
  Конкатенация векторов (их длины складываются).
-}
(+++) :: Vec n a -> Vec m a -> Vec (n + m) a
Nil       +++ bs =              bs
(a :> as) +++ bs = a :> (as +++ bs)

instance Functor (Vec n) where
  fmap f = \case
    Nil     -> Nil
    x :> xs -> f x :> fmap f xs

instance Foldable (Vec n) where
  foldr _ z Nil = z
  foldr f z (x :> xs) = f x (foldr f z xs)