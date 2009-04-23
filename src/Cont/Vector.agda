module Cont.Vector (α : Set) where

open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Data.Product
open import Cont

Vector : ℕ → Set
Vector zero    = Cont ⊤              (λ _ → ⊥) α
Vector (suc n) = Cont (α × Vector n) (λ _ → ⊥) α

[] : Vector zero
[] = tt ▹ λ()

infixr 5 _∷_
_∷_ : ∀ {n}
    → α
    → Vector n
    → Vector (suc n)
x ∷ xs = (x , xs) ▹ λ()
