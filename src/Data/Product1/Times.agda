module Data.Product1.Times where
open import Data.Product1

infixr 2 _×₁₁_
_×₁₁_ : Set1 → Set1 → Set1
α ×₁₁ β = Σ₁₁ α (λ _ → β)
