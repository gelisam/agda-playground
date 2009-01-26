module Data.Product1.Exists where
open import Data.Product1

∃₀₁ : {A : Set } → (A → Set1) → Set1
∃₀₁ = Σ₀₁ _

∃₁₀ : {A : Set1} → (A → Set ) → Set1
∃₁₀ = Σ₁₀ _

∃₁₁ : {A : Set1} → (A → Set1) → Set1
∃₁₁ = Σ₁₁ _
