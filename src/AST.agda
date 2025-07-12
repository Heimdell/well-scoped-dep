
module AST where

open import Data.Nat
open import Data.Vec as Vec hiding ([_])
open import Data.String
open import Data.Product using (_×_; _,_)
open import Function

module Thinning where

  variable
    A : Set
    as bs cs ds Γ Δ Φ : ℕ
    a b : A

  data _⊆_ : ℕ -> ℕ -> Set where
    []  :           0      ⊆ 0
    -∷_ : as ⊆ bs →     as ⊆ suc bs
    +∷_ : as ⊆ bs → suc as ⊆ suc bs

  infixr 5 -∷_ +∷_


  𝟏-⊆_ : (as : ℕ) → Set
  𝟏-⊆ as = 1 ⊆ as

  𝟎-⊆-Γ : 0 ⊆ Γ
  𝟎-⊆-Γ {(zero)} = []
  𝟎-⊆-Γ {suc Γ}  = -∷ 𝟎-⊆-Γ

  Γ-⊆-Γ : Γ ⊆ Γ
  Γ-⊆-Γ {(zero)} = []
  Γ-⊆-Γ {suc Γ}  = +∷ Γ-⊆-Γ

  _∙_ : Γ ⊆ Δ → Δ ⊆ Φ → Γ ⊆ Φ
  ([]   ) ∙  []     = []
  (   gd) ∙ (-∷ df) = -∷ (gd ∙ df)
  (-∷ gd) ∙ (+∷ df) = -∷ (gd ∙ df)
  (+∷ gd) ∙ (+∷ df) = +∷ (gd ∙ df)

  _[_] : Vec A Γ → 𝟏-⊆ Γ → A
  (x ∷ xs) [ -∷ var ] = xs [ var ]
  (x ∷ xs) [ +∷ var ] = x

open Thinning

module Name where

  record Name : Set where
    constructor ♯
    field
      name : String

open Name

module Scoped where


  data Expr (Γ : ℕ) : Set where
    var    : 𝟏-⊆ Γ → Expr Γ

    u      : Expr Γ

    pi     : (arg : Name) (ty : Expr Γ) (res : Expr (suc Γ)) → Expr Γ
    sigma  : (fst : Name) (ty : Expr Γ) (snd : Expr (suc Γ)) → Expr Γ
    eq     : (A x y : Expr Γ) → Expr Γ

    lam    : (arg : Name) (body : Expr (suc Γ)) → Expr Γ
    pair   : (fst snd : Expr Γ) → Expr Γ
    refl   : (point : Expr Γ) → Expr Γ

    app    : (f x : Expr Γ) → Expr Γ
    uncur  : (fst snd : Name) (p : Expr Γ) (k : Expr (2 + Γ)) → Expr Γ
    transp : (A x y P px ex : Expr Γ) → Expr Γ

    letRec :
      (decls : Vec (Name × Expr (Δ + Γ) × Expr Γ) Δ)
      (body  : Expr (Δ + Γ))
             → Expr Γ


module Runtime where

  Env        : (Γ : ℕ) → Set
  data Neutral (Γ : ℕ) : Set


  data Err : Set where
    not-a-function not-a-pair not-a-refl : Err

  data Value (Γ : ℕ) : Set


  _⇶_ : (Γ Δ : ℕ) → Set


  data Value Γ where
    neutral : (n : Neutral Γ)
                 → Value Γ

    u       : Value Γ

    pi      : (arg : Name) (ty : Value Γ) (res : Value (suc Γ)) → Value Γ
    sigma   : (arg : Name) (ty : Value Γ) (res : Value (suc Γ)) → Value Γ
    eq      : (A x y : Value Γ) → Value Γ

    lam     : (arg  : Name)
              (body : Value (suc Γ))
                    → Value Γ

    pair    : (fst snd : Value Γ) → Value Γ
    refl    : (point   : Value Γ) → Value Γ

    err     : Err → Value Γ

    delay   : Δ ⇶ Γ → Value Δ → Value Γ

  Env Γ = Vec (Value Γ) Γ


  data Neutral Γ where
    var   : 𝟏-⊆ Γ → Neutral Γ

    app   : (f : Neutral Γ)
            (x : Value Γ)
               → Neutral Γ

    uncur : (fst snd : Name)
            (p       : Neutral Γ)
            (k       : Value (2 + Γ))
                     → Neutral Γ

    transp : (A x y P px : Value Γ)
             (eq         : Neutral Γ)
                         → Neutral Γ


  Γ ⇶ Δ = Vec (Value Δ) Γ

  thin    : Γ ⊆ Δ → Value   Γ → Value   Δ
  thin-∅  : Γ ⊆ Δ → Neutral Γ → Neutral Δ
  subst   : Γ ⇶ Δ → Value   Γ → Value   Δ
  subst-∅ : Γ ⇶ Δ → Neutral Γ → Value   Δ
  Γ⇶Γ     : Γ ⇶ Γ


  suc-⇶ : Γ ⇶ Δ → suc Γ ⇶ suc Δ
  suc-⇶ sub = neutral (var (+∷ 𝟎-⊆-Γ)) ∷ Vec.map (thin (-∷ Γ-⊆-Γ)) sub

  _⊙_ : Γ ⇶ Δ → Δ ⇶ Φ → Γ ⇶ Φ
  _⊙_ = {!   !}


  thin th (neutral n)          = neutral (thin-∅ th n)
  thin th (lam     arg body)   = lam      arg (thin (+∷ th) body)
  thin th (pair    fst snd)    = pair    (thin th fst) (thin th snd)
  thin th (refl    point)      = refl    (thin th point)
  thin th (err     error)      = err      error
  thin th  u                   = u
  thin th (pi      arg ty res) = pi       arg (thin th ty) (thin (+∷ th) res)
  thin th (sigma   arg ty res) = sigma    arg (thin th ty) (thin (+∷ th) res)
  thin th (eq      A x y)      = eq      (thin th A) (thin th x) (thin th y)
  thin th (delay   sub val)    = {!   !}

  thin-∅ th (var    v)            = var   (v ∙ th)
  thin-∅ th (app    n x)          = app   (thin-∅ th n) (thin th x)
  thin-∅ th (uncur  fst snd n k)  = uncur  fst snd (thin-∅ th n) (thin (+∷ +∷ th) k)
  thin-∅ th (transp A x y P px n) =
    transp
      (thin th A)
      (thin th x)
      (thin th y)
      (thin th P)
      (thin th px)
      (thin-∅ th n)

  {-# TERMINATING #-}
  subst sub (neutral n)          = subst-∅ sub n
  subst sub (lam     arg body)   = lam    arg (subst (suc-⇶ sub) body)
  subst sub (pair    fst snd)    = pair  (subst sub fst) (subst sub snd)
  subst sub (refl    point)      = refl  (subst sub point)
  subst sub (err     error)      = err    error
  subst sub  u                   = u
  subst sub (pi      arg ty res) = pi     arg (subst sub ty) (subst (suc-⇶ sub) res)
  subst sub (sigma   arg ty res) = sigma  arg (subst sub ty) (subst (suc-⇶ sub) res)
  subst sub (eq      A x y)      = eq    (subst sub A) (subst sub x) (subst sub y)
  subst sub (delay   sub′ val)   = delay (sub′ ⊙ sub) val


  apply : Value Γ → Value Γ → Value Γ
  apply (neutral n       ) x = neutral (app n x)
  apply (lam     arg body) x = subst (x ∷ Γ⇶Γ) body
  apply (delay   sub val)  x = apply (subst sub val) x
  apply (err     error   ) x = err error
  apply (_               ) x = err not-a-function


  uncurry : Name → Name → Value Γ → Value (2 + Γ) → Value Γ
  uncurry fst snd (neutral n      ) k = neutral (uncur fst snd n k)
  uncurry _   _   (pair    fst snd) k = subst (snd ∷ fst ∷ Γ⇶Γ) k
  uncurry fst snd (delay   sub val) k = uncurry fst snd (subst sub val) k
  uncurry _   _   (err     error  ) k = err error
  uncurry _   _   (_              ) k = err not-a-pair


  transport : (A x y P px : Value Γ) (n : Value Γ) → Value Γ
  transport A x y P px (neutral n)     = neutral (transp A x y P px n)
  transport A x y P px (refl    point) = px
  transport A x y P px (delay sub val) = transport A x y P px (subst sub val)
  transport A x y P px (err     error) = err error
  transport A x y P px  _              = err not-a-refl


  subst-∅ sub (var    ptr)          = sub [ ptr ]
  subst-∅ sub (app    val x)        = apply (subst-∅ sub val) (subst sub x)
  subst-∅ sub (uncur  fst snd p k)  = uncurry fst snd (subst-∅ sub p) (subst (suc-⇶ (suc-⇶ sub)) k)
  subst-∅ sub (transp A x y P px p) =
    transport
      (subst sub A)
      (subst sub x)
      (subst sub y)
      (subst sub P)
      (subst sub px)
      (subst-∅ sub p)


  Γ⇶Γ {(zero)} = []
  Γ⇶Γ {suc Γ} = neutral (var (+∷ 𝟎-⊆-Γ)) ∷ Vec.map (thin (-∷ Γ-⊆-Γ)) Γ⇶Γ


module Eval where

  open Scoped
  open Runtime

  -- retract : Vec (Value (Δ + Γ)) Δ → Vec (Value Γ) Δ
  -- retract [] = []
  -- retract (decl ∷ decls) = {!   !} ∷ {!   !}

  {-# TERMINATING #-}
  eval : Expr Γ → Value Γ
  eval (var    ptr)          = neutral (var ptr)
  eval  u                    = u
  eval (pi     arg ty res)   = pi arg (eval ty) (eval res)
  eval (sigma  fst ty snd)   = sigma fst (eval ty) (eval snd)
  eval (eq     A x y)        = eq (eval A) (eval x) (eval y)
  eval (lam    arg body)     = lam arg (eval body)
  eval (pair   fst snd)      = pair (eval fst) (eval snd)
  eval (refl   point)        = refl (eval point)
  eval (app    f x)          = apply (eval f) (eval x)
  eval (uncur  fst snd p k)  = uncurry fst snd (eval p) (eval k)
  eval (transp A x y P px p) = transport (eval A) (eval x) (eval y) (eval P) (eval px) (eval p)
  eval {Γ} (letRec {Δ} decls k)      = do
    let
      decls′ : Δ ⇶ (Δ + Γ)
      decls′ = Vec.map (λ (name , val , ty) → eval val) decls
    subst {!   !} (eval k)
    -- let decls″ = retract decls′
    -- subst (decls″ Vec.++ Γ⇶Γ) (eval k)