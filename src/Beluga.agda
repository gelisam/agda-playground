module Beluga where

open import Data.List1
open import Data.List1.In
open import Data.List1.All2
open import Data.HList
open import Data.Pat
open import Data.Product1
open import Data.Product1.Times
open import Data.Product1.Exists
open import Relation.Unary.Surjective1

-- a possibly incomplete list of pattern-matching attempts
Case : Set → Set1
Case α = List₁ (Pat α)

-- This should really be a (co?)record, but Agda2 doesn't treat records
-- coinductively as far as productivity checking goes, AFAICT
mutual
  Downward : {α : Set} → Case α → Set2
  Downward case = All₁₂ (λ p → All₁₂ Cover (pat-dom p)) case

  Complete : {α : Set} → Case α → Set1
  Complete {α} case = Surjective₁₀ construct where
    construct : (∃₁₁ λ p → p ∈ case ×₁₁ HList (pat-dom p)) → α
    construct p,∈,xs = pat-apply p xs where
      p = proj₁₁₁ p,∈,xs
      ∈,xs = proj₁₁₂ p,∈,xs
      xs = proj₁₁₂ ∈,xs

  codata Cover (cod : Set) : Set2 where
    covers : (case     : Case cod)
           → (downward : Downward case)
           → (complete : Complete case)
           → Cover cod

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
_∶_ : {α : Set} (p : α) (α' : Type α) → Pat (ret-t α')
_∶_ p α' = arg-t α' , apply p
