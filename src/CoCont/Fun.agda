module CoCont.Fun where

open import Data.Unit
open import Data.Fin
open import CoCont

Fun : Set → Set → Set
Fun α β = CoCont ⊤ α (λ _ → β)

make-fun : ∀ {α β}
         → (α → β)
         → Fun α β
make-fun f = tt ▹ f

app : ∀ {α β}
    → Fun α β
    → α → β
app (tt ▹ f) x = f x
