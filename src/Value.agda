module Value where

open import Context
open import Term


data Value : {τ : Type} → ε ⊦ τ term → Set where
  unit : Value unit
  ƛ    : ∀ {τ₁ τ₂}
       → (e : ε ▸ τ₁ ⊦ τ₂ term)
       → Value (ƛ e)

data ⊦_value (τ : Type) : Set where
  value : {e : ε ⊦ τ term}
        → Value e
        → ⊦ τ value

value➝term : ∀ {τ}
           →   ⊦ τ value
           → ε ⊦ τ term
value➝term (value {e} _) = e
