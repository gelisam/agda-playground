module CoCont.List (α : Set) where

open import Data.Unit
open import Data.Nat
open import Data.Vec
open import CoCont

List : Set
List = CoCont ℕ ⊤ (Vec α)

[]L : List
[]L = 0 ▹ (λ _ → [])

infixr 5 _∷L_
_∷L_ : α → List → List
x ∷L (n ▹ xs) = n′ ▹ xs′ where
  n′ : ℕ
  n′ = suc n
  
  xs′ : ⊤ → Vec α n′
  xs′ tt = x ∷ xs tt
