module CoCont.Vector (α : Set) where

open import Data.Unit
open import Data.Nat
open import Data.Fin
open import CoCont

Vector : ℕ → Set
Vector n = CoCont ⊤ (Fin n) (λ _ → α)

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