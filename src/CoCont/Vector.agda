module CoCont.Vector (α : Set) where

open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Data.Fin
open import Data.Product
open import CoCont

Vector : ℕ → Set
Vector n = CoCont ⊤ (λ _ → α) (Fin n)

[] : Vector zero
[] = tt ▹ λ()

infixr 5 _∷_
_∷_ : ∀ {n}
    → α
    → Vector n
    → Vector (suc n)
_∷_ {n} x (tt ▹ lookup) = tt ▹ lookup′ where
  lookup′ : Fin (suc n) → α
  lookup′ zero    = x
  lookup′ (suc i) = lookup i
