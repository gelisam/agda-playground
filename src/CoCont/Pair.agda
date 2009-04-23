module CoCont.Pair where

open import Data.Unit
open import Data.Fin
open import CoCont

Pair : Set → Set → Set
Pair α β = CoCont α ⊤ (λ _ → β)

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