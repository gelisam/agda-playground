module Relation.Binary.HeterogeneousEquality.Dependent where

open import Relation.Binary.HeterogeneousEquality


Dependent-Substitutive : {a : Set}
                       → {b : a → Set}
                       → (P : (x : a) → b x → Set)
                       → Set
Dependent-Substitutive {a} {b} P = {x₁ x₂ : a}
                                 → x₁ ≅ x₂
                                 → {y₁ : b x₁}
                                 → {y₂ : b x₂}
                                 → y₁ ≅ y₂
                                 → P x₁ y₁
                                 → P x₂ y₂

dependent-subst : {a : Set}
                → {b : a → Set}
                → (P : (x : a) → b x → Set)
                → Dependent-Substitutive P
dependent-subst P refl refl p = p

_Dependent-Preserves : {a : Set}
                     → {b : a → Set}
                     → {c : (x : a) → (y : b x) → Set}
                     → (f : (x : a) → (y : b x) → c x y)
                     → Set
_Dependent-Preserves {a} {b} _+_ = {x₁ x₂ : a}
                                 → x₁ ≅ x₂
                                 → {y₁ : b x₁}
                                 → {y₂ : b x₂}
                                 → y₁ ≅ y₂
                                 → x₁ + y₁ ≅ x₂ + y₂

Dependent-Congruential : Set1
Dependent-Congruential = {a : Set}
                       → {b : a → Set}
                       → {c : (x : a) → (y : b x) → Set}
                       → (f : (x : a) → (y : b x) → c x y)
                       → f Dependent-Preserves

dependent-cong : Dependent-Congruential
dependent-cong f {x₁} ≅1 {y₁} ≅2 =
  dependent-subst (λ x₂ y₂ → f x₁ y₁ ≅ f x₂ y₂) ≅1 ≅2 refl
