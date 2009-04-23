module FCont.List (α : Set) where

open import Data.Nat
open import Data.Fin
open import FCont

List : Set
List = FCont ℕ (λ x → x) α

[] : List
[] = 0 ▹ ⟦_⟧ where
  ⟦_⟧ : Fin 0 → α
  ⟦ () ⟧

infixr 5 _∷_
_∷_ : α → List → List
x ∷ (n ▹ lookup) = n′ ▹ lookup′ where
  n′ : ℕ
  n′ = suc n
  
  lookup′ : Fin n′ → α
  lookup′ zero    = x
  lookup′ (suc i) = lookup i
