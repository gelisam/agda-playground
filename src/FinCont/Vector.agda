module FinCont.Vector (α : Set) where

open import Data.Unit
open import Data.Nat
open import Data.Fin
open import FinCont

Vector : ℕ → Set
Vector n = FinCont ⊤ (λ _ → n) α

[] : Vector zero
[] = tt ▹ lookup where
  lookup : Fin 0 → α
  lookup ()

infixr 5 _∷_
_∷_ : ∀ {n}
    → α
    → Vector n
    → Vector (suc n)
_∷_ {n} x (tt ▹ lookup) = tt ▹ lookup′ where
  lookup′ : Fin (suc n) → α
  lookup′ zero    = x
  lookup′ (suc i) = lookup i
