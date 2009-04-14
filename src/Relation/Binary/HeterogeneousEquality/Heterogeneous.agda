module Relation.Binary.HeterogeneousEquality.Heterogeneous where

open import Relation.Binary.HeterogeneousEquality


coherence : ∀ {a : Set}
          → (P : a → Set)
          → {x₁ x₂ : a}
          → (x₁≅x₂ : x₁ ≅ x₂)
          → (y : P x₁)
          → subst P x₁≅x₂ y ≅ y
coherence P refl y = refl


_Heterogeneous-Preserves : {a : Set}
                         → {b : a → Set}
                         → (f : (x : a) → b x)
                         → Set
_Heterogeneous-Preserves {a} f = {x₁ x₂ : a}
                               →   x₁ ≅   x₂
                               → f x₁ ≅ f x₂

Heterogeneous-Congruential : Set1
Heterogeneous-Congruential = {a : Set}
                           → {b : a → Set}
                           → (f : (x : a) → b x)
                           → f Heterogeneous-Preserves

heterogeneous-cong : Heterogeneous-Congruential
heterogeneous-cong f {x} x≅y =
  subst (λ y → f x ≅ f y) x≅y refl
