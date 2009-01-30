module Relation.Unary.Surjective1 where
open import Data.Product
open import Data.Product1.Exists
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality1

Surjective₁₀ : {α : Set1}{β : Set} → (α → β) → Set1
Surjective₁₀ f = ∀ y → ∃₁₀ λ x → f x ≡ y

Surjective₀₁ : {α : Set}{β : Set1} → (α → β) → Set1
Surjective₀₁ {α} {β} f = (y : β) → Σ α λ x → f x ≡₁ y

Surjective₁₁ : {α β : Set1} → (α → β) → Set1
Surjective₁₁ f = ∀ y → ∃₁₀ λ x → f x ≡₁ y

