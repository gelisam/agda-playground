module Value where

open import Context
open import Term


data Value : {τ : Type} → ε ⊦ τ term → Set where
  unit : Value unit
  ƛ    : ∀ {τ₁ τ₂}
       → (e : ε ▸ τ₁ ⊦ τ₂ term)
       → Value (ƛ e)
