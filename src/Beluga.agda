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
open import Relation.Unary.Surjective1
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

-- This should really be a (co?)record, but Agda2 doesn't treat records
-- coinductively as far as productivity checking goes, AFAICT
mutual
  Downward : {α : Set} → DDecl α → Set2
  Downward ddecl = All₁₂ (λ c → All₁₂ ↓DDecl (dom c)) ddecl

  Complete : {α : Set} → DDecl α → Set1
  Complete {α} ddecl = Surjective₁₀ construct where
    construct : (∃₁₁ λ c → c ∈ ddecl ×₁₁ hdom c) → α
    construct c,∈,xs = con c xs where
      c = proj₁₁₁ c,∈,xs
      ∈,xs = proj₁₁₂ c,∈,xs
      xs = proj₁₁₂ ∈,xs

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
    complete tt = (_
                  , here
                  , [])
                , refl

-- case n : ℕ of
--   box(. U[.]) ⇒ ...
pat-U-ℕ-↓DDecl : ↓DDecl ℕ
pat-U-ℕ-↓DDecl ~ is-↓DDecl ddecl downward complete
  where
    ddecl = id ∶ ℕ ⇾ # ℕ
          ∷ []

    downward : Downward ddecl
    downward = (pat-U-ℕ-↓DDecl ∷ [])
             ∷ []

    complete : Complete ddecl
    complete n = (_
                 , here
                 , n ∷ [])
               , refl

-- case n : ℕ of
--   box(. zero) ⇒ ...
--   box(. suc U[.]) ⇒ ...
pat-z-s-ℕ-↓DDecl : ↓DDecl ℕ
pat-z-s-ℕ-↓DDecl ~ is-↓DDecl ddecl downward complete
  where
    ddecl = zero ∶ # ℕ
          ∷ suc  ∶ ℕ ⇾ # ℕ
          ∷ []

    downward : Downward ddecl
    downward = []
             ∷ (pat-z-s-ℕ-↓DDecl ∷ [])
             ∷ []

    complete : Complete ddecl
    complete zero    = (_
                       , here
                       , [])
                     , refl
    complete (suc n) = (_
                       , there here
                       , n ∷ [])
                     , refl

×-↓DDecl : {α β : Set} → ↓DDecl α → ↓DDecl β → ↓DDecl (α × β)
×-↓DDecl {α} {β} ↓α ↓β ~ is-↓DDecl ddecl downward complete
  where
    pair = _,_

    ddecl = pair ∶ α ⇾ β ⇾ # (α × β)
          ∷ []

    downward : Downward ddecl
    downward = (↓α ∷ ↓β ∷ [])
             ∷ []

    complete : Complete ddecl
    complete ( a , b ) = (_
                         , here
                         , a ∷ b ∷ [])
                         , refl

data Tree (α : Set) : Set where
  Branch : Tree α → α → Tree α → Tree α
  Leaf   : Tree α

Tree-↓DDecl : {α : Set} -> ↓DDecl α → ↓DDecl (Tree α)
Tree-↓DDecl {α} ↓α ~ is-↓DDecl ddecl downward complete
  where

    ddecl = Branch ∶ Tree α ⇾ α ⇾ Tree α ⇾ # Tree α
          ∷ Leaf   ∶ # Tree α
          ∷ []

    downward : Downward ddecl
    downward = (Tree-↓DDecl ↓α ∷ ↓α ∷ Tree-↓DDecl ↓α ∷ [])
             ∷ []
             ∷ []

    complete : Complete ddecl
    complete (Branch l x r) = (_
                              , here
                              , l ∷ x ∷ r ∷ [])
                            , refl
    complete Leaf           = (_
                              , there here
                              , [])
                            , refl
