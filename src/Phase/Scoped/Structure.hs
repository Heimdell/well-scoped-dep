{-# LANGUAGE DataKinds #-}

{- |
  Well-scoped модель языка с завтипами.

  Помимо зависимых произведений, содержит зависимые суммы и пропозициональное
  равенство, вместе с конструкторами и элиминаторами.

  Уровни вселенных отсутствуют, постулируется `U : U`.

  Доступна неограниченная взаимная рекурсия.

  Структура скоупов рекурсии следующая:

  > ...prog<ctx>
  >
  > let rec <d>
  >   foo : ...ty<ctx>
  >   foo = ...expr<d + ctx>
  >
  >   bar : ...ty<ctx>
  >   bar = ...expr<d + ctx>
  >
  > ...prog<d + ctx>

  По-видимому, сделать на этом HIT не получится.
-}
module Phase.Scoped.Structure
  ( Expr (..)
  ) where

import Data.Nat
import Data.Thin
import Data.Vec
import Data.Name

{- |
  Программа на моделируемом языке.
-}
data Expr (n :: Nat)
  = -- | Переменная
    ExprVar
      { var :: Below n }

  | -- | Универсум
    --   @Type@
    ExprU

  | -- | Зависимое произведение
    --   @Π[ argName : argTy ] resTy@
    ExprPi
      { argName :: Name
      , argTy   :: Expr    n
      , resTy   :: Expr (S n)
      }

  | -- | Зависимая сумма
    --   @Σ[ fstName : fstTy ] sndTy@
    ExprSigma
      { fstName :: Name
      , fstTy   :: Expr    n
      , sndTy   :: Expr (S n)
      }

  | -- | Пропозициональное равенство
    --   @<ty> x = y@
    ExprEq
      { x, y :: Expr n }

  | -- | Лямбда-функция
    --   @\argName -> body@
    ExprLam
      { argName :: Name
      , body    :: Expr (S n)
      }

  | -- | Завиcимая пара
    --   @fst, snd@
    ExprPair
      { fst, snd :: Expr n }

  | -- | Доказательство равенства
    --   @refl@
    ExprRefl

  | -- | Элиминатор функции
    --   @f x@
    ExprApp { f, x :: Expr n }

  | -- | Элиминатор пары
    --   @let fstName, sndName = pair in consume@
    ExprUncurry
      { fstName, sndName :: Name
      , pair             :: Expr       n
      , consume          :: Expr (S (S n))
      }

  | ExprTransp
      { a, x, y, p, px, eq :: Expr n }

  |  -- | Взаимно-рекурсивные объявления
     --   > let rec
     --   >   [decl : ty = val]
     --   > rest
     --   >
     forall d
  .  ExprLetRec
      { d         :: NatS d
      , declNames :: Vec d  Name
      , declTys   :: Vec d (Expr      n)
      , declVals  :: Vec d (Expr (d + n))
      , rest      ::        Expr (d + n)
      }
