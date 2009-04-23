module FlatCont.Pair where

open import Data.Unit
open import Data.Fin
open import FlatCont

Pair : Set → Set → Set
Pair α β = FlatCont α ⊤ β

make-pair : ∀ {α β}
          → α
          → β
          → Pair α β
make-pair x y = x ▹ (λ _ → y)

proj₁ : ∀ {α β}
      → Pair α β
      → α
proj₁ (x ▹ y) = x

proj₂ : ∀ {α β}
      → Pair α β
      → β
proj₂ (x ▹ y) = y tt
