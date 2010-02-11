------------------------------------------------------------------------
-- Propositional equality
------------------------------------------------------------------------

module Relation.Binary.PropositionalEquality2 where

open import Relation.Nullary
open import Relation.Binary

------------------------------------------------------------------------
-- Propositional equality

infix 4 _≡₂_ _≢₂_

data _≡₂_ {a : Set2} (x : a) : a → Set where
  refl : x ≡₂ x

-- Nonequality.

_≢₂_ : {a : Set2} → a → a → Set
x ≢₂ y = ¬ x ≡₂ y

------------------------------------------------------------------------
-- Some properties

reflexive : ∀ {a} (x : a) → x ≡₂ x
reflexive _ = refl

sym : ∀ {a} {x y : a} → x ≡₂ y → y ≡₂ x
sym refl = refl

trans : ∀ {a} {x y z : a} → x ≡₂ y → y ≡₂ z → x ≡₂ z
trans refl refl = refl

subst : {a b : Set1} → a ≡₂ b → a → b
subst refl x = x

cong : ∀ {a b} (f : a → b) → ∀ {x y} → x ≡₂ y → f x ≡₂ f y
cong _ refl = refl

cong₂ : ∀ {a b c} (f : a → b → c) →
        ∀ {x₁ x₂ y₁ y₂} → x₁ ≡₂ x₂ → y₁ ≡₂ y₂ → f x₁ y₁ ≡₂ f x₂ y₂
cong₂ _ refl refl = refl
