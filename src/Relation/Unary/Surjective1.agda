module Relation.Unary.Surjective1 where
open import Data.Product
open import Data.Product1.Exists
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality1

Surjective₁₀ : ∀ {α β} → (α → β) → Set1
Surjective₁₀ f = ∀ y → ∃₁₀ λ x → f x ≡ y

Surjective₀₁ : ∀ {α β} → (α → β) → Set1
Surjective₀₁ f = ∀ y → ∃   λ x → f x ≡₁ y

Surjective₁₁ : ∀ {α β} → (α → β) → Set1
Surjective₁₁ f = ∀ y → ∃₁₀ λ x → f x ≡₁ y

