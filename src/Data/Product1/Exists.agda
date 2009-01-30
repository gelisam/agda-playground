module Data.Product1.Exists where
open import Data.Product1

∃₀₁ : ∀ {A} → (A → Set1) → Set1
∃₀₁ = Σ₀₁ _

∃₁₀ : ∀ {A} → (A → Set ) → Set1
∃₁₀ = Σ₁₀ _

∃₁₁ : ∀ {A} → (A → Set1) → Set1
∃₁₁ = Σ₁₁ _
