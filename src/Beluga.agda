module Beluga where

open import Data.Function hiding (_∶_)
open import Data.List1
open import Data.Nat
open import Data.Product
open import Data.Product1
open import Data.Unit
open import Relation.Binary.PropositionalEquality

data HList : List₁ Set → Set1 where
  []  : HList []

  _∷_ : {α : Set} {Δ : List₁ Set}
      → (x : α)
      → HList Δ
      → HList (α ∷ Δ)

infix 4 _∈_
data _∈_ {α : Set1} : α → List₁ α → Set1 where
  here  : ∀ {x}   {xs : List₁ α}                 → x ∈ x ∷ xs
  there : ∀ {x y} {xs : List₁ α} (x∈xs : x ∈ xs) → x ∈ y ∷ xs

infixr 2 _×₁₁_
_×₁₁_ : Set1 → Set1 → Set1
α ×₁₁ β = Σ₁₁ α (λ _ → β)

record Con (cod : Set) : Set1 where
  field
    dom   : List₁ Set

  hdom : Set1
  hdom = HList dom

  field
    con  : hdom → cod

open Con

Data : Set → Set1
Data α = List₁ (Con α)

Realizes : {α : Set} → Con α → α → Set1
Realizes c x = Σ₁₀ (hdom c) λ xs → con c xs ≡ x

infixr 5 _∷_
data All₁₂ {α : Set1} (P : α → Set2) : List₁ α → Set2 where 
  []  : All₁₂ P []

  _∷_ : ∀ {x xs}
      → P x
      → All₁₂ P      xs
      → All₁₂ P (x ∷ xs) 

-- This should really be a (co?)record, but Agda2 doesn't treat records
-- coinductively as far as productivity checking goes, AFAICT
mutual
  Downward : {α : Set} → Data α → Set2
  Downward data' = All₁₂ (λ c → All₁₂ ↓Data (dom c)) data'

  Complete : {α : Set} → Data α → Set1
  Complete {α} data' = (x : α) → Σ₁₁ (Con α) (λ c → c ∈ data' ×₁₁ Realizes c x)

  codata ↓Data (cod : Set) : Set2 where 
    is-↓Data : (data'    : Data cod)
             → (downward : Downward data')
             → (complete : Complete data')
             → ↓Data cod

infixr 7 _⇾_
data Type : Set → Set1 where
  #_  : (α : Set) → Type α
  _⇾_ : (α : Set) {β : Set} → Type β → Type (α → β)

arg-ts : {α : Set} → Type α → List₁ Set
arg-ts (# _)   = []
arg-ts (α ⇾ β) = α ∷ arg-ts β

base-t : {α : Set} → Type α → Set
base-t (# α)   = α
base-t (α ⇾ β) = base-t β

apply : {α : Set} {α' : Type α} → α → HList (arg-ts α') → base-t α'
apply {α' = # α}   f []       = f
apply {α' = α ⇾ β} f (x ∷ xs) = apply (f x) xs

infix 6 _∶_
_∶_ : {α : Set} (c : α) (α' : Type α) → Con (base-t α')
_∶_ c α' = record { dom = arg-ts α'; con = apply c }

⊤-↓Data : ↓Data ⊤
⊤-↓Data = is-↓Data data' downward complete
  where
    data' = tt ∶ # ⊤
          ∷ []

    downward : Downward data'
    downward = [] ∷ []

    complete : Complete data'
    complete tt = tt ∶ # ⊤
                , here
                , []
                , ≡-refl

ℕ-↓Data : ↓Data ℕ
ℕ-↓Data ~ is-↓Data data' downward complete
  where
    data' = zero ∶ # ℕ
          ∷ suc  ∶ ℕ ⇾ # ℕ
          ∷ []

    downward : Downward data'
    downward = []
             ∷ (ℕ-↓Data ∷ [])
             ∷ []

    complete : Complete data'
    complete zero    = zero ∶ # ℕ
                     , here
                     , []
                     , ≡-refl
    complete (suc n) = suc  ∶ ℕ ⇾ # ℕ
                     , there here
                     , n ∷ []
                     , ≡-refl

×-↓Data : ↓Data (ℕ × ℕ)
×-↓Data ~ is-↓Data data' downward complete
  where
    pair = _,_

    data' = pair ∶ ℕ ⇾ ℕ ⇾ # (ℕ × ℕ)
          ∷ []

    downward : Downward data'
    downward = (ℕ-↓Data ∷ ℕ-↓Data ∷ [])
             ∷ []

    complete : Complete data'
    complete ( n₁ , n₂ ) = pair ∶ ℕ ⇾ ℕ ⇾ # (ℕ × ℕ)
                         , here
                         , n₁ ∷ n₂ ∷ []
                         , ≡-refl

data Tree : Set where
  Branch : Tree → ℕ → Tree → Tree
  Leaf   : Tree

Trees-↓Data : ↓Data Tree
Trees-↓Data ~ is-↓Data data' downward complete
  where

    data' = Branch ∶ Tree ⇾ ℕ ⇾ Tree ⇾ # Tree
          ∷ Leaf   ∶ # Tree
          ∷ []

    downward : Downward data'
    downward = (Trees-↓Data ∷ ℕ-↓Data ∷ Trees-↓Data ∷ [])
             ∷ []
             ∷ []

    complete : Complete data'
    complete (Branch l x r) = Branch ∶ Tree ⇾ ℕ ⇾ Tree ⇾ # Tree
                            , here
                            , l ∷ x ∷ r ∷ []
                            , ≡-refl
    complete Leaf           = Leaf ∶ # Tree
                            , there here
                            , []
                            , ≡-refl

-- data Pattern {A : Set} : Deconstructible↓ A → Set2 where
--   var : {fs : List₁ (Con A)}
--       → {all : All₁₂ (λ f → Deconstructible↓ (dom f)) fs}
--       → {exh : ((x : A) → Σ₁₁ (Con A) (λ f → f ∈ fs ×₁₀ CanConstruct f x))}
--       → (f : Con A) → f ∈ fs → Pattern (deconstructible fs all exh)
--   var : {fs : List₁ (Con A)}
--       → {all : All₁₂ (λ f → Deconstructible↓ (dom f)) fs}
--       → {exh : ((x : A) → Σ₁₁ (Con A) (λ f → f ∈ fs ×₁₀ CanConstruct f x))}
--       → (f : Con A) → f ∈ fs → Pattern (deconstructible fs all exh)
