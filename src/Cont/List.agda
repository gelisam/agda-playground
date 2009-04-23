module Cont.List (α : Set) where

open import Data.Nat
open import Data.Fin
open import Cont

List : Set
List = Cont ℕ Fin α

[] : List
[] = 0 ▹ λ()

infixr 5 _∷_
_∷_ : α → List → List
x ∷ (n ▹ lookup) = n′ ▹ lookup′ where
  n′ : ℕ
  n′ = suc n
  
  lookup′ : Fin n′ → α
  lookup′ zero    = x
  lookup′ (suc i) = lookup i
