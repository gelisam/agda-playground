module Relation.Binary.HeterogeneousEquality.Coherence where

open import Relation.Binary.HeterogeneousEquality


coherence : ∀ {a : Set}
          → (P : a → Set)
          → {x₁ x₂ : a}
          → (x₁≅x₂ : x₁ ≅ x₂)
          → (y : P x₁)
          → subst P x₁≅x₂ y ≅ y
coherence P refl y = refl
