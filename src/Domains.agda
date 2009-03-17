{- Copyright (c) 2009, Darin Morrison
   All rights reserved.
  
   Redistribution and use in source and binary forms, with or without
   modification, are permitted provided that the following conditions are met:
  
   - Redistributions of source code must retain the above copyright notice,
     this list of conditions and the following disclaimer.
   - Redistributions in binary form must reproduce the above copyright notice,
     this list of conditions and the following disclaimer in the documentation
     and/or other materials provided with the distribution.
   - The names of contributors may not be used to endorse or promote products
     derived from this software without specific prior written permission.
  
   THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
   AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
   IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
   ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
   LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR 
   CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
   SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
   INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
   CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
   ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
   POSSIBILITY OF SUCH DAMAGE.
-}

{-# OPTIONS --no-positivity-check #-}

module Domains where

--------------------------------------------------------------------------------
-- Operation Properties

Op₂ : Set → Set
Op₂ α = α → α → α

--------------------------------------------------------------------------------
-- Relation Properties

Rel : Set → Set1
Rel α = α → α → Set

module Relations {α : Set} (_≈_ : Rel α) where

  Antisymmetric : Rel α → Set
  Antisymmetric _R_ = ∀ {x y} → x R y → y R x → x ≈ y

  Reflexive : Rel α → Set
  Reflexive _R_ = ∀ {x} → x R x

  Transitive : Rel α → Set
  Transitive _R_ = ∀ {x y z} → x R y → y R z → x R z

  record ChainRel : Set1 where
    carrier : Set
    carrier = α
    field
      _≤_     : Rel carrier
      antisym : Antisymmetric _≤_
      trans   : Transitive    _≤_

open Relations

--------------------------------------------------------------------------------
-- Chains

module Chains {α : Set} {_≈_ : Rel α} (R : ChainRel _≈_) where
  open import Data.Nat
    hiding (_≤_; fold)
  open import Data.Product
  open import Data.Unit
    hiding (_≤_)

  open ChainRel _≈_ R

  mutual
    -- A Chain is a list containing proofs that each element is less
    -- than the its immediate successor.
    data Chain : ℕ → Set where
      []    : Chain 0
      _∷_,_ : ∀ {n} (x : carrier) (xs : Chain n) (p : x ≼ xs) → Chain (suc n)

    _≼_ : ∀ {n} → carrier → Chain n → Set
    _ ≼ []           = ⊤
    x ≼ (x′ ∷ _ , _) = x ≤ x′

  head : ∀ {n} → Chain (suc n) → carrier
  head (x ∷ _ , _) = x

  data _∈_ : ∀ {n} → carrier → Chain n → Set where
    here  : ∀ {x    n} {xs : Chain n} {p} → x ∈ (x ∷ xs , p) 
    there : ∀ {x x′ n} {xs : Chain n} {p} (x∈xs : x ∈ xs) → x ∈ (x′ ∷ xs , p)

--------------------------------------------------------------------------------
-- ωChains

module ωChains {α : Set} {_≈_ : Rel α} (R : ChainRel _≈_) where
  open import Coinduction
  open import Data.Nat
    renaming (_≤_ to _≤ℕ_)
  open import Data.Product
    renaming (_×_ to _∧_)
  open import Data.Unit
    hiding   (_≤_)

  open ChainRel _≈_ R
  open Chains       R
    hiding   (head; _∈_)
    renaming (_≼_ to _≼′_)

  mutual
    -- An ωChain is a stream containing proofs that each element is less
    -- than the its immediate successor.
    -- NOTE: fails positivity check because of (xω : ∞ ωChain)
    data ωChain : Set where
      _∷_,_ : ∀ (x : carrier) (xω : ∞ ωChain) (p : x ≼ xω) → ωChain

    head : ωChain → carrier
    head (x ∷ _ , _) = x

    _≼_ : carrier → ∞ ωChain → Set
    x ≼ xω = x ≤ head (♭ xω)

  -- Convert a finite prefix of an ω-Chain to a Chain

  mutual
    take : (n : ℕ) → ωChain → Chain n
    take zero    _ = []
    take (suc n) (x ∷ xω , p) = x ∷ take n (♭ xω) , convert n xω p

    convert : ∀ {x} n xω → x ≤ head (♭ xω) → x ≼′ take n (♭ xω)
    convert zero    _   _ = tt
    convert (suc n) xω p with ♭ xω
    ... | _ ∷ _ , _       = p

  data _∈_ : carrier → ωChain → Set where
    here  : ∀ {x    xω}   → x ∈ xω
    there : ∀ {x x′ xω p} → x ∈ ♭ xω → x ∈ (x′ ∷ xω , p)

  UpperBound : carrier → ωChain → Set
  UpperBound x xω = ∀ {y} → y ∈ xω → y ≤ x

  LeastUpperBound : carrier → ωChain → Set
  LeastUpperBound x xω = UpperBound x xω
                       ∧ (∀ {x′} → UpperBound x′ xω → x ≤ x′)

--------------------------------------------------------------------------------
-- Domains

module Domains {α : Set} {_≈_ : Rel α} (R : ChainRel _≈_) where
  open ChainRel  _≈_ R
    renaming (_≤_ to _⊑_)
  open ωChains       R

  record IsDomain
    (_⊑_ : Rel carrier)
    (⊥   : carrier)
    (_⊔_ : Op₂ carrier)
    (⊔ω  : ωChain → carrier)
    (_⊓_ : Op₂ carrier)
    : Set where
    field
      ⊑-Reflexive  : Reflexive _≈_ _⊑_
      ⊥-is-least   : ∀ {x} → ⊥ ⊑ x
      poset→⊔-semi : ∀ {x₁ x₂} → x₁ ⊑ x₂ → x₁ ⊑ (x₁ ⊔ x₂)
      poset→⊓-semi : ∀ {x₁ x₂} → x₁ ⊑ x₂ → (x₁ ⊓ x₂) ⊑ x₂
      sup-is-lub   : ∀ {xω} → LeastUpperBound (⊔ω xω) xω

  record Domain : Set1 where
    field
      ⊥        : carrier
      _⊔_      : Op₂ carrier
      ⊔ω       : ωChain → carrier
      _⊓_      : Op₂ carrier
      isDomain : IsDomain _⊑_ ⊥ _⊔_ ⊔ω _⊓_

--------------------------------------------------------------------------------
-- Delay Structure and Basic Operations

module Delay where
  open import Coinduction
  open import Data.Nat

  data Delay (α : Set) : Set where
    now   : α → Delay α
    later : ∞ (Delay α) → Delay α

  -- The infinitely delayed computation.

  never : ∀ {α} → Delay α
  never = later never′
    where
      never′ ~ ♯ never

  -- Given two computations, choose the one that finishes first (left-biased).

  race : ∀ {α} → Delay α → Delay α → Delay α
  race (now   v₁) _          = now v₁
  race _          (now   v₂) = now v₂
  race (later d₁) (later d₂) = later race′
    where
      race′ ~ ♯ race (♭ d₁) (♭ d₂)

  -- Given two computations, choose the one that finishes last (right-biased).

  wait : ∀ {α} → Delay α → Delay α → Delay α
  wait (now   _ ) d₂         = d₂
  wait d₁         (now   _ ) = d₁
  wait (later d₁) (later d₂) = later wait′
    where
      wait′ ~ ♯ wait (♭ d₁) (♭ d₂)

  -- Peel off at most n "later" constructors.

  run_for_steps : ∀ {α} → Delay α → ℕ → Delay α
  run now   a for n     steps = now   a
  run later d for zero  steps = later d
  run later d for suc n steps = run (♭ d) for n steps

--------------------------------------------------------------------------------
-- Termination

module Termination where
  open import Coinduction
  open import Data.Nat
  open import Data.Product
  open import Data.Sum
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary

  open Delay

  -- "Terminates With"

  data _⇣_ {α : Set} : Delay α → α → Set where
    ⇣-now   : ∀ {v}
            → now v ⇣ v

    ⇣-later : ∀ {d v}
            → ♭ d ⇣ v
            → later d ⇣ v

  ⇣-inv : ∀ {α} {d} {v : α} → later d ⇣ v → ♭ d ⇣ v
  ⇣-inv (⇣-later ♭d⇣v) = ♭d⇣v

  -- How many steps until termination

  numSteps : ∀ {α} {d : Delay α} {v} → d ⇣ v → ℕ
  numSteps ⇣-now         = 0
  numSteps (⇣-later d⇣v) = suc (numSteps d⇣v)

  -- "Terminates"

  _∃⇣ : {α : Set} → Delay α → Set
  d ∃⇣ = ∃ λ v → d ⇣ v

  -- Uniqueness of termination

  ⇣-unique : {α : Set} {d : Delay α} {v₁ v₂ : α}
           → d ⇣ v₁
           → d ⇣ v₂
           → v₁ ≡ v₂
  ⇣-unique  ⇣-now              ⇣-now         = refl
  ⇣-unique (⇣-later {d} d⇣v₁) (⇣-later d⇣v₂) with ⇣-unique d⇣v₁ d⇣v₂
  ... | refl = refl

  -- A computation is "Safe" iff it yields a value after running for a
  -- finite number of steps.

  Safe : {α : Set} → Delay α → Set
  Safe d = ∃ λ n → ∃ λ v → run d for n steps ≡ now v

  -- If a computation terminates, it is safe.

  ∃⇣-safe : {α : Set} (d : Delay α) → d ∃⇣ → Safe d
  ∃⇣-safe .(now   v) (v , ⇣-now)           = 0 , v , refl
  ∃⇣-safe .(later d) (v , ⇣-later {d} d⇣v) with ∃⇣-safe (♭ d) (v , d⇣v)
  ... | n , v′ , eq                        = suc n , v′ , eq

  -- never doesn't terminate.

  ¬never⇣ : {α : Set} {v : α} → ¬ (never ⇣ v)
  ¬never⇣ never⇣v with ∃⇣-safe _ (_ , never⇣v)
  ¬never⇣ never⇣v     | zero , _ , ()
  ¬never⇣ (⇣-later p) | _    , _ , _  = ¬never⇣ p

  -- If a race of two computations terminates, then one of those
  -- computations must terminate.

  race⇣⊎ : ∀ {α} {d₁ d₂ : Delay α} {v} → race d₁ d₂ ⇣ v → d₁ ⇣ v ⊎ d₂ ⇣ v
  race⇣⊎ {α} {now   .v₁} {_}         (⇣-now   {v₁}) = inj₁ ⇣-now
  race⇣⊎ {α} {later  d₁} {now   .v₂} (⇣-now   {v₂}) = inj₂ ⇣-now
  race⇣⊎ {α} {later  d₁} {later  d₂} (⇣-later race⇣)
    with race⇣⊎ {α} {♭ d₁} {♭ d₂} race⇣
  ... | inj₁ ♭d₁⇣v = inj₁ (⇣-later ♭d₁⇣v)
  ... | inj₂ ♭d₂⇣v = inj₂ (⇣-later ♭d₂⇣v)

--------------------------------------------------------------------------------
-- Ordering

module Ordering where
  open import Coinduction
  open import Relation.Nullary.Negation

  open Delay
  open Termination

  -- d₁ ⊑ d₂ iff whenever d₁ terminates with v, d₂ also terminates with v.

  data _⊑_ {α : Set} : Delay α → Delay α → Set where
    ⊑-intro : ∀ {d₁ d₂}
            → (∀ v → d₁ ⇣ v → d₂ ⇣ v)
            → d₁ ⊑ d₂

  ⊑-inv : ∀ {α : Set} {d₁ d₂ : Delay α} → d₁ ⊑ d₂ → ∀ v → d₁ ⇣ v → d₂ ⇣ v
  ⊑-inv (⊑-intro f) = f

  -- ⊑ is reflexive

  ⊑-refl : {α : Set} {d : Delay α} → d ⊑ d
  ⊑-refl = ⊑-intro λ _ d⇣v → d⇣v

  -- ⊑ is transitive

  ⊑-trans : {α : Set} {d₁ d₂ d₃ : Delay α} → d₁ ⊑ d₂ → d₂ ⊑ d₃ → d₁ ⊑ d₃
  ⊑-trans (⊑-intro f₁) (⊑-intro f₂) = ⊑-intro (λ _ d₁⇣v → f₂ _ (f₁ _ d₁⇣v))

  -- never is the least element

  never⊑d : {α : Set} {d : Delay α} → never ⊑ d
  never⊑d = ⊑-intro (λ _ never⇣ → contradiction never⇣ ¬never⇣)

  later-⊑-later : {α : Set} {d₁ d₂ : ∞ (Delay α)}
                → later d₁ ⊑ later d₂
                → ♭ d₁ ⊑ ♭ d₂
  later-⊑-later (⊑-intro f) = ⊑-intro (λ _ ♭d₁⇣v → ⇣-inv (f _ (⇣-later ♭d₁⇣v)))

  later-⊑ : {α : Set} {d₁ : ∞ (Delay α)} {d₂ : Delay α}
          → later d₁ ⊑ d₂
          → ♭ d₁ ⊑ d₂
  later-⊑ (⊑-intro f) = ⊑-intro (λ _ ♭d₁⇣v → f _ (⇣-later ♭d₁⇣v))

--------------------------------------------------------------------------------
-- Equivalence

module Equivalence where
  open Delay
  open Ordering

  -- Identifies computations with different finite delays.

  data _≃_ {α : Set} : Delay α → Delay α → Set where
    ≃-antisym : ∀ {d₁ d₂}
              → d₁ ⊑ d₂
              → d₂ ⊑ d₁
              → d₁ ≃ d₂

  ≃-⊑ : {α : Set} {d₁ d₂ : Delay α} → d₁ ≃ d₂ → d₁ ⊑ d₂
  ≃-⊑ (≃-antisym ⊑ _) = ⊑

  ≃-⊒ : {α : Set} {d₁ d₂ : Delay α} → d₁ ≃ d₂ → d₂ ⊑ d₁
  ≃-⊒ (≃-antisym _ ⊒) = ⊒

  -- ≃ is reflexive

  ≃-refl : {α : Set} {d : Delay α} → d ≃ d
  ≃-refl = ≃-antisym ⊑-refl ⊑-refl

  -- ≃ is symmetric

  ≃-sym : {α : Set} {d₁ d₂ : Delay α} → d₁ ≃ d₂ → d₂ ≃ d₁
  ≃-sym (≃-antisym d₁⊑d₂ d₂⊑d₁) = ≃-antisym d₂⊑d₁ d₁⊑d₂

  -- ≃ is transitive

  ≃-trans : {α : Set} {d₁ d₂ d₃ : Delay α} → d₁ ≃ d₂ → d₂ ≃ d₃ → d₁ ≃ d₃
  ≃-trans (≃-antisym d₁⊑d₂ d₂⊑d₁) (≃-antisym d₂⊑d₃ d₃⊑d₂) =
    ≃-antisym (⊑-trans d₁⊑d₂ d₂⊑d₃) (⊑-trans d₃⊑d₂ d₂⊑d₁)

  ≃-resp-⊑ : {α : Set} {d₁ d₂ d₃ : Delay α} → d₁ ≃ d₂ → d₃ ⊑ d₁ → d₃ ⊑ d₂
  ≃-resp-⊑ (≃-antisym (⊑-intro f₁) _) (⊑-intro f₃) =
    ⊑-intro (λ _ d₃⇣v → f₁ _ (f₃ _ d₃⇣v))

  ≃-resp-⊒ : {α : Set} {d₁ d₂ d₃ : Delay α} → d₁ ≃ d₂ → d₁ ⊑ d₃ → d₂ ⊑ d₃
  ≃-resp-⊒ (≃-antisym _ (⊑-intro f₂)) (⊑-intro f₃) =
    ⊑-intro (λ _ d₂⇣v → f₃ _ (f₂ _ d₂⇣v))

--------------------------------------------------------------------------------
-- Domain Instances

module delayDomain (α : Set) where
  open Delay
  open Equivalence
  open Ordering

  ⊑-Rel : ChainRel (_≃_ {α})
  ⊑-Rel = record
    { _≤_     = _⊑_
    ; antisym = ≃-antisym
    ; trans   = ⊑-trans
    }

  open Domains  ⊑-Rel

  delayDomain : Domain
  delayDomain = record
    { ⊥        = never
    ; _⊔_      = race
    ; ⊔ω       = ωrace
    ; _⊓_      = wait
    ; isDomain = record
      { ⊑-Reflexive  = ⊑-refl
      ; ⊥-is-least   = never⊑d
      ; poset→⊔-semi = poset→⊔-semi
      ; poset→⊓-semi = poset→⊓-semi
      ; sup-is-lub   = {!!}
      }
    }
    where
      open import Coinduction
      open import Data.Nat
        hiding (fold)
      open import Data.Product
      open import Data.Sum
      open import Relation.Binary.PropositionalEquality

      open Chains  ⊑-Rel
        hiding (head)
      open ωChains ⊑-Rel
      open Termination

      case : {d₁ d₂ d₃ : Delay α} → d₁ ⊑ d₃ → d₂ ⊑ d₃ → race d₁ d₂ ⊑ d₃
      case (⊑-intro f₁) (⊑-intro f₂) = ⊑-intro (case′ f₁ f₂)
        where
          case′ : {d₁ d₂ d₃ : Delay α}
                → ((v : α) →      d₁    ⇣ v → d₃ ⇣ v)
                → ((v : α) →         d₂ ⇣ v → d₃ ⇣ v)
                → ((v : α) → race d₁ d₂ ⇣ v → d₃ ⇣ v)
          case′ {now   v₁}                 d₁⊑d₃ _     _          race⇣v  =
            d₁⊑d₃         _ race⇣v
          case′ {later d₁} {now   v₂}      _     d₂⊑d₃ _          race⇣v  =
            d₂⊑d₃         _ race⇣v
          case′ {later d₁} {later d₂} {d₃} d₁⊑d₃ d₂⊑d₃ _ (⇣-later race⇣v) =
            case′ f₁′ f₂′ _ race⇣v
            where
              f₁′ = λ _ ♭d₁⇣v′ → d₁⊑d₃ _ (⇣-later ♭d₁⇣v′)
              f₂′ = λ _ ♭d₂⇣v′ → d₂⊑d₃ _ (⇣-later ♭d₂⇣v′)

      ωrace : ωChain → Delay α
      ωrace (now   v₁ ∷ dω , p₁) = now v₁
      ωrace (later d₁ ∷ dω , p₁) with ♭ dω
      ... | now   v₂ ∷ dω′ , p₂  = now v₂
      ... | later d₂ ∷ dω′ , p₂  = later ωrace′
        where
          ωrace′ ~ ♯ ωrace (race (♭ d₁) (♭ d₂) ∷ dω′ , p)
            where
              p = case (⊑-trans (later-⊑-later p₁) (later-⊑ p₂)) (later-⊑ p₂)

      poset→⊔-semi : {d₁ d₂ : Delay α} → d₁ ⊑ d₂ → d₁ ⊑ race d₁ d₂
      poset→⊔-semi (⊑-intro f) = ⊑-intro (lemma f)
        where
          lemma : {d₁ d₂ : Delay α }
                → ((v : α) → d₁ ⇣ v → d₂ ⇣ v)
                → ((v : α) → d₁ ⇣ v → race d₁ d₂ ⇣ v)
          lemma                       f′ v  ⇣-now         =
            ⇣-now
          lemma {later d₁} {now   v₂} f′ v          d₁⇣v  =
            f′ _ d₁⇣v
          lemma {later d₁} {later d₂} f′ v (⇣-later d₁⇣v) =
            ⇣-later (lemma f″ _ d₁⇣v)
            where
              f″ = λ _ ♭d₁⇣v′ → ⇣-inv (f′ _ (⇣-later ♭d₁⇣v′))

      poset→⊓-semi : {d₁ d₂ : Delay α} → d₁ ⊑ d₂ → wait d₁ d₂ ⊑ d₂
      poset→⊓-semi (⊑-intro f) = ⊑-intro (lemma₂ f)
        where
          lemma₁ : {d₁ d₂ : Delay α }
                 → ((v : α) → d₁ ⇣ v → d₂ ⇣ v)
                 → ((v : α) → wait d₁ d₂ ⇣ v → d₁ ⇣ v)
          lemma₁ {now   v₁}            f′ v          wait⇣v  =
            subst (_⇣_ (now v₁)) (⇣-unique (f′ _ ⇣-now) wait⇣v) ⇣-now
          lemma₁ {later d₁} {now   v₂} f′ v          wait⇣v  =
            wait⇣v
          lemma₁ {later d₁} {later d₂} f′ v (⇣-later wait⇣v) =
            ⇣-later (lemma₁ f″ _ wait⇣v)
            where
              f″ = λ _ ♭d₁⇣v′ → ⇣-inv (f′ _ (⇣-later ♭d₁⇣v′))

          lemma₂ : {d₁ d₂ : Delay α }
                 → ((v : α) → d₁ ⇣ v → d₂ ⇣ v)
                 → ((v : α) → wait d₁ d₂ ⇣ v → d₂ ⇣ v)
          lemma₂ {now   v₁}            f′ v          wait⇣v  =
            wait⇣v
          lemma₂ {later d₁} {now   v₂} f′ v          wait⇣v  =
            f′ _ wait⇣v
          lemma₂ {later d₁} {later d₂} f′ v (⇣-later wait⇣v) =
            f′ _ (⇣-later (lemma₁ f″ _ wait⇣v))
              where
                f″ = λ _ ♭d₁⇣v′ → ⇣-inv (f′ _ (⇣-later ♭d₁⇣v′))

