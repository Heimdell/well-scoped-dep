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

  , zip
  , unzip
  ) where

import Prelude hiding (zip, unzip)

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

instance Traversable (Vec n) where
  traverse f = \case
    Nil     -> pure Nil
    x :> xs -> (:>) <$> f x <*> traverse f xs

zip :: Vec n a -> Vec n b -> Vec n (a, b)
zip (a :> as) (b :> bs) = (a, b) :> zip as bs
zip  Nil       Nil      = Nil

unzip :: Vec n (a, b) -> (Vec n a, Vec n b)
unzip  Nil            = (Nil, Nil)
unzip ((a, b) :> ab) = (a :> as, b :> bs)
  where
    (as, bs) = unzip ab