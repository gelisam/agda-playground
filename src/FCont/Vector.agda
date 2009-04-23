module FCont.Vector (α : Set) where

open import Data.Unit
open import Data.Nat
open import Data.Fin
open import Data.Product
open import FCont

Vector : ℕ → Set
Vector zero    = FCont ⊤              (λ _ → 0) α
Vector (suc n) = FCont (α × Vector n) (λ _ → 0) α

[] : Vector zero
[] = tt ▹ ⟦_⟧ where
  ⟦_⟧ : Fin 0 → α
  ⟦ () ⟧

infixr 5 _∷_
_∷_ : ∀ {n}
    → α
    → Vector n
    → Vector (suc n)
x ∷ xs = (x , xs) ▹ ⟦_⟧ where
  ⟦_⟧ : Fin 0 → α
  ⟦ () ⟧
