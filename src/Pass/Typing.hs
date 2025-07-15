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
import Unsafe.Coerce (unsafeCoerce)
import Debug.Trace (traceShowM, traceM)

type Env n = Vec n (Value n)
type Ns  n = Vec n Name

data ErrMsg
  = Err
  | CannotInferCtor Pos
  | NotAPi Doc
  | Mismatch Doc Doc
  | SkolemEscaped Pos Doc
  | IsNotOfType Doc Doc

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

type Err = (ErrMsg, Doc)

failWithEnv :: KnownNat n => Env n -> Ns n -> ErrMsg -> Either Err a
failWithEnv env ns msg = do
  throwError (msg, dumpEnv env ns)

dumpEnv :: KnownNat n => Env n -> Ns n -> Doc
dumpEnv env ns
  = vcat
  $ map do \(n, v) -> pPrint n <.> ":" \\ pic ns v
  $ toList (zip ns env)

check :: forall n. KnownNat n => Env n -> Ns n -> Value n -> Expr n -> Either Err ()
check env ns ty expr = case expr of
  ExprU -> case ty of
    ValueU -> pure ()
    other  -> do
      failWithEnv env ns $ IsNotOfType (pic ns other) "Type"

  ExprPi arg argTy res -> case ty of
    ValueU -> do
      check env ns ValueU argTy
      check
        (s' (eval argTy :> env))
                 (arg   :> ns)
                  ValueU
                  res

  ExprSigma arg argTy res -> case ty of
    ValueU -> do
      check env ns ValueU argTy
      check
        (s' (eval argTy :> env))
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
      check (s' (argTy :> env)) (arg :> ns) res body

    other -> do
      failWithEnv env ns $ IsNotOfType (pic ns other) (pic ns expr)

  ExprPair fst snd -> case ty of
    ValueSigma _ fstTy sndTy -> do
      check env ns                        fstTy  fst
      check env ns (subst (fstTy :> keep) sndTy) snd

    other -> do
      failWithEnv env ns $ IsNotOfType (pic ns other) (pic ns expr)

  ExprRefl -> case ty of
    ValueEq _ _ -> pure ()
    other -> do
      failWithEnv env ns $ IsNotOfType (pic ns other) (pic ns expr)

  ExprLetRec @_ @d dNs tys vals k -> do
    -- get declaration names (dNs) and types (dEnv)
    dEnv <- for tys (assertTypeAndEval env ns)

    for_ (zip dEnv vals) \(ty', val) -> do
      check
        (sn' @d (dEnv +++ env))
                (dNs  +++ ns)
        (sn  @d  ty')
                 val

    check @(d + n)
      (sn' @d (dEnv +++ env))
              (dNs  +++ ns)
              (thin (weaken @d every) ty)
               k

  other -> do
    ty' <- infer env ns other
    unify env ns ty ty'

infer :: forall n. KnownNat n => Env n -> Ns n -> Expr n -> Either Err (Value n)
infer env ns = \case
  ExprVar ptr -> pure (index ptr env)
  ExprApp f x -> do
    ty <- infer env ns f  -- infer function type
    case ty of
      ValuePi _ ty' res -> do  -- should be Pi-type
        check env ns ty' x
        pure (subst (eval x :> keep) res)

      other ->
        failWithEnv env ns $ NotAPi (pic ns other)

  ExprUncurry fst snd pair uncurry' -> do
    ty <- infer env ns pair
    case ty of
      ValueSigma _ fst' snd' -> do
        ty' <-
          infer
            ( s' (snd' :> s' (fst' :> env)))
            (     snd  :>     fst  :> ns)
            uncurry'

        -- check that both variables did not escape
        case independent @(S (S O)) ty' of
          Right ty'' -> pure ty''
          Left  var  ->
            failWithEnv env ns
              $ SkolemEscaped (index var (snd.pos :> fst.pos :> Nil))
                $ pic (snd :> fst :> ns) ty'

  ExprTransp a x y p px eq -> do
    _ <- check env ns  ValueU                       a   -- [A  : Type]
    _ <- check env ns (eval a)                      x   -- [x  : A]
    _ <- check env ns (eval a)                      y   -- [y  : A]
    _ <- check env ns (ValuePi "aboba" (eval a) ValueU) p   -- [P  : (x : A) -> Type]
    _ <- check env ns (apply   (eval p) (eval x))   px  -- [px : P x]
    _ <- check env ns (ValueEq (eval x) (eval y))   eq  -- [eq : x == y]
    pure (apply (eval p) (eval y))                      --    -> P y

  ExprLetRec @_ @d dNs tys vals k -> do
    -- get declaration names (dNs) and types (dEnv)
    dEnv <- for tys (assertTypeAndEval env ns)

    for_ (zip dEnv vals) \(ty, val :: Expr (d + n)) -> do
      check
        (sn' @d (dEnv +++ env))
                (dNs  +++ ns)
        (sn  @d  ty)
                 val

    ty' <- infer @(d + n)
      (sn' @d (dEnv +++ env))
              (dNs  +++ ns)
               k

    traceM "dump"
    traceShowM (pic (dNs +++ ns) ty')
    traceShowM (map pPrint (toList ns))
    traceShowM (map pPrint (toList dNs))

    case independent @d @n ty' of
      Right rest -> pure rest
      Left  used ->
        failWithEnv env ns
          $ SkolemEscaped (index used ((.pos) <$> dNs))
          $ pPrint $ index used dNs

assertTypeAndEval :: KnownNat n => Env n -> Ns n -> Expr n -> Either Err (Value n)
assertTypeAndEval env ns ty = do
  check env ns ValueU ty
  pure (eval ty)

sn :: forall d n. (KnownNat d, KnownNat n) => Value n -> Value (d + n)
sn = thin (weaken @d every)

sn' :: forall d n f. (KnownNat d, Functor f, KnownNat n) => f (Value n) -> f (Value (d + n))
sn' = fmap (sn @d)

s :: KnownNat n => Value n -> Value (S n)
s = thin (Drop every)

s' :: (KnownNat n, Functor f) => f (Value n) -> f (Value (S n))
s' = fmap s

unify :: KnownNat n => Env n -> Ns n -> Value n -> Value n -> Either Err ()
unify env ns l r = do
  unless (l == r) do
    failWithEnv env ns $ Mismatch (pic ns l) (pic ns r)

independent :: forall d' n' . (KnownNat n', KnownNat d') => Value (d' + n') -> Either (Below d') (Value n')
independent = go @d' @n'
  where
    go :: forall d n. (KnownNat n, KnownNat d) => Value (d + n) -> Either (Below d) (Value n)
    go = \case
      ValueNeutral neutral -> ValueNeutral <$> goN neutral
      ValueU               -> ValueU       <$  pure ()

      ValuePi    arg ty res -> ValuePi    arg <$> go ty <*> go (cast @_ @(S (d + n)) @(d + S n) res)
      ValueSigma arg ty res -> ValueSigma arg <$> go ty <*> go (cast @_ @(S (d + n)) @(d + S n) res)
      ValueEq    x y        -> ValueEq        <$> go x  <*> go y

      ValueLam  arg body    -> ValueLam arg <$> go (cast @_ @(S (d + n)) @(d + S n) body)
      ValuePair fst snd     -> ValuePair <$> go fst <*> go snd
      ValueRefl             -> ValueRefl <$ pure ()

    goN :: forall d n. (KnownNat n, KnownNat d) => Neutral (d + n) -> Either (Below d) (Neutral n)
    goN = \case
      NeutralVar var -> case splitVar @d @n var of
        Left  used -> Left used
        Right rest -> pure (NeutralVar rest)

      NeutralApp f x -> NeutralApp <$> goN f <*> go x

      NeutralUncurry fst snd pair uncurry' ->
        NeutralUncurry fst snd <$> goN pair <*> go (cast @_ @(S (S (d + n))) @(d + S (S n)) uncurry')

      NeutralTransp a x y p px eq ->
        NeutralTransp
          <$> go a
          <*> go x
          <*> go y
          <*> go p
          <*> go px
          <*> goN eq

cast :: forall p a b. p a -> p b
cast = unsafeCoerce