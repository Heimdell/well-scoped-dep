{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Functor law" #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Pass.Typing where

import Prelude hiding (zip, fst, snd, uncurry, unzip)

import Control.Monad.Except
import Data.Vec
import Data.Nat
import Data.Name
import Data.Thin
import Text.Pos
import Text.Pretty

import Phase.Scoped
import Phase.Runtime
import Pass.Eval
import Data.Foldable (toList, for_)
import Control.Monad (unless)
import Data.Traversable (for)

type Env n = Vec n (Value n)
type Ns  n = Vec n Name

data ErrMsg
  = Err
  | CannotInferCtor Pos
  | NotAPi Doc
  | Mismatch Doc Doc
  | SkolemEscaped Pos Doc
  | IsNotOfType Doc Doc
  | Hole Name Doc

instance Pretty ErrMsg where
  pPrint = \case
    Err -> "somthing bad has happened"
    CannotInferCtor p -> "Constructor in inferred position:" $$ pPrint p
    NotAPi doc -> "Expected function, not" $$ doc
    Mismatch l r ->
      vcat
        [ "expected"
        , nest 2 l
        , "got"
        , nest 2 r
        ]
    SkolemEscaped pos doc ->
      "Skolem variable" <+> doc <+> "escaped from" $$ pPrint pos
    IsNotOfType ty val ->
      vcat
        [ "value"
        , nest 2 val
        , "is not of type"
        , nest 2 ty
        ]
    Hole name ty -> "Typed hole: ?" <.> pPrint name <+> ":" \\ ty

type Err = (ErrMsg, Doc)

failWithEnv :: Env n -> Ns n -> ErrMsg -> Either Err a
failWithEnv env ns msg = do
  throwError (msg, dumpEnv env ns)

dumpEnv :: Env n -> Ns n -> Doc
dumpEnv env ns
  = vcat
  $ map do \(n, v) -> pPrint n <.> ":" \\ pic ns v
  $ toList (zip ns env)

check :: forall n. Env n -> Ns n -> Value n -> Expr n -> Either Err ()
check env ns ty expr = do
  let n = len env
  case expr of
    ExprU -> case ty of
      ValueU -> pure ()
      other  -> do
        failWithEnv env ns $ IsNotOfType (pic ns other) "Type"

    ExprPi arg argTy res -> case ty of
      ValueU -> do
        check env ns ValueU argTy
        check
          (s' n (eval n argTy :> env))
                       (arg   :> ns)
                        ValueU
                        res

    ExprSigma arg argTy res -> case ty of
      ValueU -> do
        check env ns ValueU argTy
        check
          (s' n (eval n argTy :> env))
                       (arg   :> ns)
                        ValueU
                        res
      other -> do
        failWithEnv env ns $ IsNotOfType (pic ns other) (pic ns expr)

    ExprEq x y -> case ty of
      ValueU -> do
        a <- infer env ns x
        check env ns a y

      other -> do
        failWithEnv env ns $ IsNotOfType (pic ns other) (pic ns expr)

    ExprLam arg body -> case ty of
      ValuePi _ argTy res -> do
        check (s' n (argTy :> env)) (arg :> ns) res body

      other -> do
        failWithEnv env ns $ IsNotOfType (pic ns other) (pic ns expr)

    ExprPair fst snd -> case ty of
      ValueSigma _ fstTy sndTy -> do
        check env ns                            fstTy  fst
        check env ns (subst n (fstTy :> keep n) sndTy) snd

      other -> do
        failWithEnv env ns $ IsNotOfType (pic ns other) (pic ns expr)

    ExprRefl -> case ty of
      ValueEq _ _ -> pure ()
      other -> do
        failWithEnv env ns $ IsNotOfType (pic ns other) (pic ns expr)

    ExprHole name -> do
      failWithEnv env ns $ Hole name (pic ns ty)

    ExprLetRec d dNs tys vals k -> do
      -- get declaration names (dNs) and types (dEnv)
      dEnv <- for tys (assertTypeAndEval env ns)

      for_ (zip dEnv vals) \(ty', val) -> do
        check
          (sn' d n (dEnv +++ env))
                   (dNs  +++ ns)
          (sn  d n  ty')
                    val

      check
        (sn' d n (dEnv +++ env))
                 (dNs  +++ ns)
                 (thin (weaken d (every n)) ty)
                  k

    other -> do
      ty' <- infer env ns other
      unify env ns ty ty'

infer :: forall n. Env n -> Ns n -> Expr n -> Either Err (Value n)
infer env ns expr = do
  let n = len env
  case expr of
    ExprVar ptr -> pure (index ptr env)
    ExprApp f x -> do
      ty <- infer env ns f  -- infer function type
      case ty of
        ValuePi _ ty' res -> do  -- should be Pi-type
          check env ns ty' x
          pure (subst n (eval n x :> keep n) res)

        other ->
          failWithEnv env ns $ NotAPi (pic ns other)

    ExprUncurry fst snd pair uncurry' -> do
      ty <- infer env ns pair
      case ty of
        ValueSigma _ fst' snd' -> do
          ty' <-
            infer
              (s' (NatS n) (snd' :> s' n (fst' :> env)))
              (             snd  :>       fst  :> ns)
              uncurry'

          -- check that both variables did not escape
          case independent (NatS (NatS NatO)) n ty' of
            Right ty'' -> pure ty''
            Left  var  ->
              failWithEnv env ns
                $ SkolemEscaped (index var (snd.pos :> fst.pos :> Nil))
                  $ pic (snd :> fst :> ns) ty'

    ExprTransp a x y p px eq -> do
      _ <- check env ns  ValueU                             a   -- [A  : Type]
      _ <- check env ns (eval n a)                          x   -- [x  : A]
      _ <- check env ns (eval n a)                          y   -- [y  : A]
      _ <- check env ns (ValuePi "aboba" (eval n a) ValueU) p   -- [P  : (x : A) -> Type]
      _ <- check env ns (apply n (eval n p) (eval n x))     px  -- [px : P x]
      _ <- check env ns (ValueEq (eval n x) (eval n y))     eq  -- [eq : x == y]
      pure (apply n (eval n p) (eval n y))                      --    -> P y

    ExprLetRec d dNs tys vals k -> do
      -- get declaration names (dNs) and types (dEnv)
      dEnv <- for tys (assertTypeAndEval env ns)

      for_ (zip dEnv vals) \(ty, val) -> do
        check
          (sn' d n (dEnv +++ env))
                  (dNs  +++ ns)
          (sn  d n  ty)
                    val

      ty' <- infer
        (sn' d n (dEnv +++ env))
                (dNs  +++ ns)
                  k

      case independent d n ty' of
        Right rest -> pure rest
        Left  used ->
          failWithEnv env ns
            $ SkolemEscaped (index used ((.pos) <$> dNs))
            $ pPrint $ index used dNs

assertTypeAndEval :: Env n -> Ns n -> Expr n -> Either Err (Value n)
assertTypeAndEval env ns ty = do
  check env ns ValueU ty
  pure (eval (len env) ty)

sn :: forall d n. NatS d -> NatS n -> Value n -> Value (d + n)
sn d n = thin (weaken d (every n))

sn' :: forall d n f. (Functor f) => NatS d -> NatS n -> f (Value n) -> f (Value (d + n))
sn' = (fmap .) . sn

s :: NatS n -> Value n -> Value (S n)
s = thin . Drop . every

s' :: (Functor f) => NatS n -> f (Value n) -> f (Value (S n))
s' = fmap . s

unify :: Env n -> Ns n -> Value n -> Value n -> Either Err ()
unify env ns l r = do
  unless (l == r) do
    failWithEnv env ns $ Mismatch (pic ns l) (pic ns r)

independent :: forall d' n' . NatS d' -> NatS n' -> Value (d' + n') -> Either (Below d') (Value n')
independent = go
  where
    go :: forall d n. NatS d -> NatS n -> Value (d + n) -> Either (Below d) (Value n)
    go d n = \case
      ValueNeutral neutral -> ValueNeutral <$> goN d n neutral
      ValueU               -> ValueU       <$  pure ()

      ValuePi    arg ty res -> ValuePi    arg <$> go d n ty <*> go d (NatS n) (swap (NatS NatO) d n res)
      ValueSigma arg ty res -> ValueSigma arg <$> go d n ty <*> go d (NatS n) (swap (NatS NatO) d n res)
      ValueEq    x y        -> ValueEq        <$> go d n x  <*> go d n y

      ValueLam  arg body    -> ValueLam arg <$> go d (NatS n) (swap (NatS NatO) d n body)
      ValuePair fst snd     -> ValuePair <$> go d n fst <*> go d n snd
      ValueRefl             -> ValueRefl <$ pure ()

    goN :: forall d n. NatS d -> NatS n -> Neutral (d + n) -> Either (Below d) (Neutral n)
    goN d n = \case
      NeutralVar var -> case splitVar d var of
        Left  used -> Left used
        Right rest -> pure (NeutralVar rest)

      NeutralApp f x -> NeutralApp <$> goN d n f <*> go d n x

      NeutralUncurry fst snd pair uncurry' ->
        NeutralUncurry fst snd <$> goN d n pair <*> go d (NatS (NatS n)) (swap (NatS (NatS NatO)) d n uncurry')

      NeutralTransp a x y p px eq ->
        NeutralTransp
          <$> go  d n a
          <*> go  d n x
          <*> go  d n y
          <*> go  d n p
          <*> go  d n px
          <*> goN d n eq

swap :: forall d x n. NatS x -> NatS d -> NatS n -> Value (x + (d + n)) -> Value (d + (x + n))
swap x' d' n' = subst (add d' (add x' n')) (x +++ (d +++ n))
  where
    d :: Subst d (d + (x + n))
    d = fmap (thin (weakenr (add x' n') (every d'))) (keep d')

    x :: Subst x (d + (x + n))
    x = fmap (thin (weaken d' (weakenr n' (every x')))) (keep x')

    n :: Subst n (d + (x + n))
    n = fmap (thin (weaken d' (weaken x' (every n')))) (keep n')
