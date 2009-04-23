module DiCont.Sigma where

open import Data.Unit
open import Data.Fin
open import DiCont

Σ : (α : Set) → (α → Set) → Set
Σ α β = DiCont α (λ _ → ⊤) β

make-pair : ∀ {α β}
          → (a : α)
          → (b : β a)
          → Σ α β
make-pair x y = x ▹ (λ _ → y)

proj₁ : ∀ {α β}
      → Σ α β
      → α
proj₁ (x ▹ y) = x

proj₂ : ∀ {α β}
      → (s : Σ α β)
      → β (proj₁ s)
proj₂ (x ▹ y) = y tt
