module Relation.Unary.Surjective where
open import Data.Product
open import Relation.Binary.PropositionalEquality

Surjective : {α β : Set} → (α → β) → Set
Surjective f = ∀ y → ∃ λ x → f x ≡ y
