module Weak.List (α : Set) where
open import Data.Unit
open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Sum

import Weak

⟦_⟧ : ⊤ ⊎ α → ℕ
⟦ inj₁ tt ⟧ = 0
⟦ inj₂ x  ⟧ = 1

open Weak (⊤ ⊎ α) ⟦_⟧


List : Set
List = Weak

ε : List
ε = sup (inj₁ tt) (childs 0)

infixr 5 _∷_
_∷_ : α → List → List
_∷_ x xs = sup (inj₂ x) (childs 1 xs)
