module Beluga where

open import Data.Function hiding (_∶_)
open import Data.List1
open import Data.List1.In
open import Data.List1.All2
open import Data.HList
open import Data.Nat
open import Data.Product
open import Data.Product1
open import Data.Product1.Times
open import Data.Product1.Exists
open import Data.Unit
open import Relation.Binary.PropositionalEquality

record Con (cod : Set) : Set1 where
  field
    dom   : List₁ Set

  hdom : Set1
  hdom = HList dom

  field
    con  : hdom → cod

open Con

DDecl : Set → Set1
DDecl α = List₁ (Con α)

Realizes : {α : Set} → Con α → α → Set1
Realizes c x = ∃₁₀ λ xs → con c xs ≡ x

-- This should really be a (co?)record, but Agda2 doesn't treat records
-- coinductively as far as productivity checking goes, AFAICT
mutual
  Downward : {α : Set} → DDecl α → Set2
  Downward ddecl = All₁₂ (λ c → All₁₂ ↓DDecl (dom c)) ddecl

  Complete : {α : Set} → DDecl α → Set1
  Complete {α} ddecl = (x : α) → ∃₁₁ λ c → c ∈ ddecl ×₁₁ Realizes c x

  codata ↓DDecl (cod : Set) : Set2 where
    is-↓DDecl : (ddecl    : DDecl cod)
              → (downward : Downward ddecl)
              → (complete : Complete ddecl)
              → ↓DDecl cod

infixr 7 _⇾_
data Type : Set → Set1 where
  #_  : (α : Set) → Type α
  _⇾_ : (α : Set) {β : Set} → Type β → Type (α → β)

arg-t : {α : Set} → Type α → List₁ Set
arg-t (# _)   = []
arg-t (α ⇾ β) = α ∷ arg-t β

ret-t : {α : Set} → Type α → Set
ret-t (# α)   = α
ret-t (α ⇾ β) = ret-t β

apply : {α : Set} {α' : Type α} → α → HList (arg-t α') → ret-t α'
apply {α' = # α}   f []       = f
apply {α' = α ⇾ β} f (x ∷ xs) = apply (f x) xs

infix 6 _∶_
_∶_ : {α : Set} (c : α) (α' : Type α) → Con (ret-t α')
_∶_ c α' = record { dom = arg-t α'; con = apply c }

⊤-↓DDecl : ↓DDecl ⊤
⊤-↓DDecl = is-↓DDecl ddecl downward complete
  where
    ddecl = tt ∶ # ⊤
          ∷ []

    downward : Downward ddecl
    downward = [] ∷ []

    complete : Complete ddecl
    complete tt = tt ∶ # ⊤
                , here
                , []
                , refl

ℕ-↓DDecl : ↓DDecl ℕ
ℕ-↓DDecl ~ is-↓DDecl ddecl downward complete
  where
    ddecl = zero ∶ # ℕ
          ∷ suc  ∶ ℕ ⇾ # ℕ
          ∷ []

    downward : Downward ddecl
    downward = []
             ∷ (ℕ-↓DDecl ∷ [])
             ∷ []

    complete : Complete ddecl
    complete zero    = zero ∶ # ℕ
                     , here
                     , []
                     , refl
    complete (suc n) = suc  ∶ ℕ ⇾ # ℕ
                     , there here
                     , n ∷ []
                     , refl

×-↓DDecl : ↓DDecl (ℕ × ℕ)
×-↓DDecl ~ is-↓DDecl ddecl downward complete
  where
    pair = _,_

    ddecl = pair ∶ ℕ ⇾ ℕ ⇾ # (ℕ × ℕ)
          ∷ []

    downward : Downward ddecl
    downward = (ℕ-↓DDecl ∷ ℕ-↓DDecl ∷ [])
             ∷ []

    complete : Complete ddecl
    complete ( n₁ , n₂ ) = pair ∶ ℕ ⇾ ℕ ⇾ # (ℕ × ℕ)
                         , here
                         , n₁ ∷ n₂ ∷ []
                         , refl

data Tree : Set where
  Branch : Tree → ℕ → Tree → Tree
  Leaf   : Tree

Trees-↓DDecl : ↓DDecl Tree
Trees-↓DDecl ~ is-↓DDecl ddecl downward complete
  where

    ddecl = Branch ∶ Tree ⇾ ℕ ⇾ Tree ⇾ # Tree
          ∷ Leaf   ∶ # Tree
          ∷ []

    downward : Downward ddecl
    downward = (Trees-↓DDecl ∷ ℕ-↓DDecl ∷ Trees-↓DDecl ∷ [])
             ∷ []
             ∷ []

    complete : Complete ddecl
    complete (Branch l x r) = Branch ∶ Tree ⇾ ℕ ⇾ Tree ⇾ # Tree
                            , here
                            , l ∷ x ∷ r ∷ []
                            , refl
    complete Leaf           = Leaf ∶ # Tree
                            , there here
                            , []
                            , refl

-- data Pattern {A : Set} : Deconstructible↓ A → Set2 where
--   var : {fs : List₁ (Con A)}
--       → {all : All₁₂ (λ f → Deconstructible↓ (dom f)) fs}
--       → {exh : ((x : A) → Σ₁₁ (Con A) (λ f → f ∈ fs ×₁₀ CanConstruct f x))}
--       → (f : Con A) → f ∈ fs → Pattern (deconstructible fs all exh)
--   var : {fs : List₁ (Con A)}
--       → {all : All₁₂ (λ f → Deconstructible↓ (dom f)) fs}
--       → {exh : ((x : A) → Σ₁₁ (Con A) (λ f → f ∈ fs ×₁₀ CanConstruct f x))}
--       → (f : Con A) → f ∈ fs → Pattern (deconstructible fs all exh)
