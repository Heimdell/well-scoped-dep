
module Phase.Raw.Structure where

import Data.Name
import Text.Pos

data Expr = (:@) { pos :: Pos, expr :: Expr_ }

{- |
  Программа на моделируемом языке.
-}
data Expr_
  = -- | Переменная
    ExprVar
      { var :: Name }

  | -- | Универсум
    --   @Type@
    ExprU

  | -- | Зависимое произведение
    --   @Π[ argName : argTy ] resTy@
    ExprPi
      { argName :: Name
      , argTy   :: Expr
      , resTy   :: Expr
      }

  | -- | Зависимая сумма
    --   @Σ[ fstName : fstTy ] sndTy@
    ExprSigma
      { fstName :: Name
      , fstTy   :: Expr
      , sndTy   :: Expr
      }

  | -- | Пропозициональное равенство
    --   @<ty> x = y@
    ExprEq
      { x, y :: Expr }

  | -- | Лямбда-функция
    --   @\argName -> body@
    ExprLam
      { argName :: Name
      , body    :: Expr
      }

  | -- | Завиcимая пара
    --   @fst, snd@
    ExprPair
      { fst, snd :: Expr }

  | -- | Доказательство равенства
    --   @refl@
    ExprRefl

  | -- | Элиминатор функции
    --   @f x@
    ExprApp     { f, x :: Expr }

  | -- | Элиминатор пары
    --   @let fstName, sndName = pair in consume@
    ExprUncurry { fstName, sndName :: Name, pair :: Expr, consume :: Expr }
  | ExprTransp  { a, x, y, p, px, eq :: Expr }

  | ExprHole Name

  |  -- | Взаимно-рекурсивные объявления
     --   > let rec
     --   >   [decl : ty = val]
     --   > rest
     --   >
    ExprLetRec
      { decls :: [(Name, Expr, Expr)]
      , rest  :: Expr
      }
