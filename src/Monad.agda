
module Monad where

open import Function

private variable
  A B : Set
  M S : Set → Set

record Functor (S : Set → Set) : Set₁ where
  field
    map : (A → B) → S A → S B
open Functor ⦃...⦄ public

record Applicative (S : Set → Set) : Set₁ where
  field
    ⦃ functor ⦄ : Functor S
    _<*>_ : S (A → B) → S A → S B
    pure  : A → S A
open Applicative ⦃...⦄ public

record Alternative (S : Set → Set) : Set₁ where
  field
    ⦃ applicative ⦄ : Applicative S
    ∅     : S A
    _<|>_ : S A → S A → S A
open Alternative ⦃...⦄ public

record Monad (S : Set → Set) : Set₁ where
  field
    ⦃ applicative ⦄ : Applicative S
    _>>=_ : S A → (A → S B) → S B
open Monad ⦃...⦄ public

record Semigroup (A : Set) : Set where
  field
    _◇_ : A → A → A
open Semigroup ⦃...⦄ public

record Monoid (A : Set) : Set where
  field
    ⦃ semigroup ⦄ : Semigroup A
    𝟏 : A
open Monoid ⦃...⦄ public

record Foldable (S : Set → Set) : Set₁ where
  field
    fold-map : ⦃ _ : Monoid B ⦄ → (A → B) → S A → B
open Foldable ⦃...⦄ public

record Traversable (S : Set → Set) : Set₁ where
  field
    ⦃ functor ⦄ : Functor S
    traverse : ⦃ _ : Monad M ⦄ → (A → M B) → S A → M (S B)
open Traversable ⦃...⦄ public

for : ⦃ _ : Traversable S ⦄ ⦃ _ : Monad M ⦄ → S A → (A → M B) → M (S B)
for = flip traverse

instance
  Monad-Semi : ⦃ _ : Applicative M ⦄ ⦃ r : Semigroup A ⦄ → Semigroup (M A)
  Monad-Semi ⦃ r ⦄ ._◇_ a b = (pure (_◇_ ⦃ r ⦄) <*> a) <*> b
  {-# INCOHERENT Monad-Semi #-}

  Monad-Monoid : ⦃ _ : Applicative M ⦄ ⦃ r : Monoid A ⦄ → Monoid (M A)
  Monad-Monoid ⦃ r ⦄ .𝟏 = pure (𝟏 ⦃ r ⦄)
  {-# INCOHERENT Monad-Monoid #-}

open import Data.List using (List; []; _∷_; foldr)
import Data.List as List

instance
  List-Functor : Functor List
  List-Functor .map = List.map

  List-Ap : Applicative List
  List-Ap ._<*>_ = List.ap
  List-Ap .pure  = _∷ []

  List-Monad : Monad List
  List-Monad ._>>=_ = flip List.concatMap

  List-Alt : Alternative List
  List-Alt .∅     = []
  List-Alt ._<|>_ = List._++_

  List-Trav : Traversable List
  List-Trav .traverse f []       = ⦇ [] ⦈
  List-Trav .traverse f (x ∷ xs) = ⦇ f x ∷ traverse f xs ⦈

  List-Semi : Semigroup (List A)
  List-Semi ._◇_ = List._++_

  List-Monoid : Monoid (List A)
  List-Monoid .𝟏 = []

  List-Foldable : Foldable List
  List-Foldable .fold-map f = foldr (_◇_ ∘ f) 𝟏

open import Data.Maybe using (Maybe; just; nothing; maybe)
import Data.Maybe as Maybe

instance
  Maybe-Functor : Functor Maybe
  Maybe-Functor .map = Maybe.map

  Maybe-Ap : Applicative Maybe
  Maybe-Ap ._<*>_ = Maybe.ap
  Maybe-Ap .pure  = just

  Maybe-Monad : Monad Maybe
  Maybe-Monad ._>>=_ = Maybe._>>=_

  Maybe-Alt : Alternative Maybe
  Maybe-Alt .∅         = nothing
  Maybe-Alt ._<|>_ a b = maybe just b a

  Maybe-Trav : Traversable Maybe
  Maybe-Trav .traverse f  nothing = ⦇ nothing    ⦈
  Maybe-Trav .traverse f (just x) = ⦇ just (f x) ⦈

  Maybe-Semi : ⦃ _ : Semigroup A ⦄ → Semigroup (Maybe A)
  Maybe-Semi ._◇_ (just a) (just b) = just (a ◇ b)
  Maybe-Semi ._◇_  a        nothing = a
  Maybe-Semi ._◇_  nothing  b       = b

  Maybe-Monoid : ⦃ _ : Semigroup A ⦄ → Monoid (Maybe A)
  Maybe-Monoid .𝟏 = nothing

  Maybe-Fold : Foldable Maybe
  Maybe-Fold .fold-map f = maybe f 𝟏

open import IO.Primitive.Core using (IO)
import IO.Primitive.Core as IO

instance
  mutual
    {-# TERMINATING #-}
    Functor-IO : Functor IO
    Functor-IO .map f ma = ⦇ f ma ⦈

    App-IO : Applicative IO
    App-IO .pure        = IO.return
    App-IO ._<*>_ mf mx = do f ← mf; x ← mx; pure (f x)

    Monad-IO : Monad IO
    Monad-IO ._>>=_ = IO._>>=_

open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
import Data.Sum as Either

private variable
  E : Set

instance
  Either-Functor : Functor (E ⊎_)
  Either-Functor .map = Either.map₂

  Either-Ap : Applicative (E ⊎_)
  Either-Ap ._<*>_ = [ const ∘ inj₁ , (λ f → [ inj₁ , inj₂ ∘ f ]) ]
  Either-Ap .pure  = inj₂

  Either-Monad : Monad (E ⊎_)
  Either-Monad ._>>=_ = [ const ∘ inj₁ , _|>_ ]

  Either-Alt : ⦃ _ : Monoid E ⦄ → Alternative (E ⊎_)
  Either-Alt .∅     = inj₁ 𝟏
  Either-Alt ._<|>_ = [ constᵣ , const ∘ inj₂ ]

  Either-Trav : Traversable (E ⊎_)
  Either-Trav .traverse f (inj₁ err) = ⦇ (inj₁    err) ⦈
  Either-Trav .traverse f (inj₂ res) = ⦇  inj₂ (f res) ⦈


  -- List-Semi : Semigroup (List A)
  -- List-Semi ._◇_ = List._++_

  -- List-Monoid : Monoid (List A)
  -- List-Monoid .𝟏 = []

  -- List-Foldable : Foldable List
  -- List-Foldable .fold-map f = foldr (_◇_ ∘ f) 𝟏

list←maybe : Maybe A → List A
list←maybe = maybe (_∷ []) []

join : ⦃ _ : Monad M ⦄ → M (M A) → M A
join mma = mma >>= id

-- data Rec (Q : Set) (R : Q → Set) (A : Set) : Set where
--   !!   : A → Rec Q R A
--   _??_ : (q : Q) (r : R q → Rec Q R A) → Rec Q R A

-- elim-rec : ∀{Q R} → (A → B) → ((r : Q) → (R r → B) → B) → Rec Q R A → B
-- elim-rec un-!! un-?? (!! x) = un-!! x
-- elim-rec un-!! un-?? (q ?? r) = un-?? q (λ t → elim-rec un-!! un-?? (r t))

-- _>>-_ : ∀{Q R} → Rec Q R A → (A → Rec Q R B) → Rec Q R B
-- ma >>- k = elim-rec k _??_ ma

-- instance
--   Functor-Rec : ∀{Q R} → Functor (Rec Q R)
--   Functor-Rec .map f (  !! x) =   !! (f x)
--   Functor-Rec .map f (q ?? r) = q ?? (map f ∘ r)

--   Applicative-Rec : ∀{Q R} → Applicative (Rec Q R)
--   Applicative-Rec ._<*>_ f x = f >>- λ f → x >>- λ x → pure (f x)
--   Applicative-Rec .pure    x = !! x

--   Monad-Rec : ∀{Q R} → Monad (Rec Q R)
--   Monad-Rec ._>>=_ = _>>-_

-- Π′ : (S : Set) (T : S → Set) → Set
-- Π′ S T = (s : S) → Rec S T (T s)

-- call : ∀{Q R} → Π′ Q R
-- call q = q ?? !!

-- morph : ∀{S T} →
--   ⦃ _ : Monad M ⦄
--   ( h : (s : S) → M (T s) )
--       → ∀{A}
--       → Rec S T A
--       → M A
-- morph h = elim-rec pure (_>>=_ ∘ h)

-- open import Data.Bool

-- halting : ∀{S} → (S → Bool) → (S → S) → Π′ S λ _ → S
-- halting stop step start with stop start
-- ... | false = !!    start
-- ... | true  = call (step start)

data Later (A : Set) : Set where
  now   :       A → Later A
  later : Later A → Later A