module DepCont.Pi where

open import Data.Unit
open import Data.Fin
open import DepCont

Π : (α : Set) → (α → Set) → Set
Π α β = DepCont ⊤ α β

make-fun : ∀ {α β}
         → ((x : α) → β x)
         → Π α β
make-fun f = tt ▹ f

app : ∀ {α β}
    → Π α β
    → (x : α) → β x
app (tt ▹ f) x = f x
