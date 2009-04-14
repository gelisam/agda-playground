------------------------------------------------------------------------
-- Properties of homogeneous binary relations
------------------------------------------------------------------------

-- This file contains some core definitions which are reexported by
-- Relation.Binary or Relation.Binary.PropositionalEquality.

module Relation.Binary.Core.Heterogeneous where

open import Data.Product
open import Data.Sum
open import Data.Function
open import Relation.Nullary.Core

------------------------------------------------------------------------
-- Heterogeneous binary relations

HRel : Set → Set → Set1
HRel a b = a → b → Set

------------------------------------------------------------------------
-- Simple properties of binary relations

infixr 4 _⇒_ _=[_/_]⇒_

-- Implication/containment. Could also be written ⊆.

_⇒_ : ∀ {a b} → HRel a b → HRel a b → Set
P ⇒ Q = ∀ {i j} → P i j → Q i j

-- Generalised implication. If P ≡ Q it can be read as "f preserves
-- P".

_=[_/_]⇒_ : ∀ {a₁ a₂ b₁ b₂}
          → HRel a₁ a₂
          → (a₁ → b₁)
          → (a₂ → b₂)
          → HRel b₁ b₂
          → Set
P =[ f / g ]⇒ Q = P ⇒ (λ x y → Q (f x) (g y))

-- -- A synonym, along with a binary variant.
-- 
-- _Preserves_⟶_ : ∀ {a₁ a₂} → (a₁ → a₂) → Rel a₁ → Rel a₂ → Set
-- f Preserves P ⟶ Q = P =[ f ]⇒ Q

_/_Preserves₂_⟶_⟶_ : ∀ {a₁ a₂ b₁ b₂ c₁ c₂}
                   → (a₁ → b₁ → c₁)
                   → (a₂ → b₂ → c₂)
                   → HRel a₁ a₂
                   → HRel b₁ b₂
                   → HRel c₁ c₂
                   → Set
_+₁_ / _+₂_ Preserves₂ P ⟶ Q ⟶ R =
  ∀ {x₁ x₂ y₁ y₂} → P x₁ x₂ → Q y₁ y₂ → R (x₁ +₁ y₁) (x₂ +₂ y₂)

-- -- Reflexivity of _∼_ can be expressed as _≈_ ⇒ _∼_, for some
-- -- underlying equality _≈_. However, the following variant is often
-- -- easier to use.
-- 
-- Reflexive : {a : Set} → (_∼_ : Rel a) → Set
-- Reflexive _∼_ = ∀ {x} → x ∼ x
-- 
-- -- Irreflexivity is defined using an underlying equality.
-- 
-- Irreflexive : {a : Set} → (_≈_ _<_ : Rel a) → Set
-- Irreflexive _≈_ _<_ = ∀ {x y} → x ≈ y → ¬ (x < y)
-- 
-- -- Generalised symmetry.
-- 
-- Sym : ∀ {a} → Rel a → Rel a → Set
-- Sym P Q = P ⇒ flip₁ Q
-- 
-- Symmetric : {a : Set} → Rel a → Set
-- Symmetric _∼_ = Sym _∼_ _∼_
-- 
-- -- Generalised transitivity.
-- 
-- Trans : ∀ {a} → Rel a → Rel a → Rel a → Set
-- Trans P Q R = ∀ {i j k} → P i j → Q j k → R i k
-- 
-- Transitive : {a : Set} → Rel a → Set
-- Transitive _∼_ = Trans _∼_ _∼_ _∼_
-- 
-- Antisymmetric : {a : Set} → (_≈_ _≤_ : Rel a) → Set
-- Antisymmetric _≈_ _≤_ = ∀ {x y} → x ≤ y → y ≤ x → x ≈ y
-- 
-- Asymmetric : {a : Set} → (_<_ : Rel a) → Set
-- Asymmetric _<_ = ∀ {x y} → x < y → ¬ (y < x)
-- 
-- _Respects_ : {a : Set} → Rel a → (a → Set) → Set
-- _∼_ Respects P = ∀ {x y} → x ∼ y → P x → P y
-- 
-- _Respects₂_ : {a : Set} → Rel a → Rel a → Set
-- ∼ Respects₂ P =
--   (∀ {x} → ∼ Respects (P x)      ) ×
--   (∀ {y} → ∼ Respects (flip₁ P y))
-- 
-- Substitutive : {a : Set} → Rel a → Set1
-- Substitutive {a} ∼ = (P : a → Set) → ∼ Respects P
-- 
-- Congruential : ({a : Set} → Rel a) → Set1
-- Congruential ∼ = ∀ {a b} → (f : a → b) → f Preserves ∼ ⟶ ∼
-- 
-- Congruential₂ : ({a : Set} → Rel a) → Set1
-- Congruential₂ ∼ =
--   ∀ {a b c} → (f : a → b → c) → f Preserves₂ ∼ ⟶ ∼ ⟶ ∼
-- 
-- Decidable : {a : Set} → Rel a → Set
-- Decidable _∼_ = ∀ x y → Dec (x ∼ y)
-- 
-- Total : {a : Set} → Rel a → Set
-- Total _∼_ = ∀ x y → (x ∼ y) ⊎ (y ∼ x)
-- 
-- data Tri (A B C : Set) : Set where
--   tri< : ( a :   A) (¬b : ¬ B) (¬c : ¬ C) → Tri A B C
--   tri≈ : (¬a : ¬ A) ( b :   B) (¬c : ¬ C) → Tri A B C
--   tri> : (¬a : ¬ A) (¬b : ¬ B) ( c :   C) → Tri A B C
-- 
-- Trichotomous : {a : Set} → Rel a → Rel a → Set
-- Trichotomous _≈_ _<_ = ∀ x y → Tri (x < y) (x ≈ y) (x > y)
--   where _>_ = flip₁ _<_
-- 
-- record NonEmpty {I : Set} (T : Rel I) : Set where
--   field
--     i     : I
--     j     : I
--     proof : T i j
-- 
-- nonEmpty : ∀ {I} {T : Rel I} {i j} → T i j → NonEmpty T
-- nonEmpty p = record { i = _; j = _; proof = p }
-- 
-- ------------------------------------------------------------------------
-- -- Propositional equality
-- 
-- -- This dummy module is used to avoid shadowing of the field named
-- -- refl defined in IsEquivalence below. The module is opened publicly
-- -- at the end of this file.
-- 
-- private
--  module Dummy where
-- 
--   infix 4 _≡_ _≢_
-- 
--   data _≡_ {a : Set} (x : a) : a → Set where
--     refl : x ≡ x
-- 
--   -- Nonequality.
-- 
--   _≢_ : {a : Set} → a → a → Set
--   x ≢ y = ¬ x ≡ y
-- 
-- ------------------------------------------------------------------------
-- -- Equivalence relations
-- 
-- -- The preorders of this library are defined in terms of an underlying
-- -- equivalence relation, and hence equivalence relations are not
-- -- defined in terms of preorders.
-- 
-- record IsEquivalence {a : Set} (_≈_ : Rel a) : Set where
--   field
--     refl  : Reflexive _≈_
--     sym   : Symmetric _≈_
--     trans : Transitive _≈_
-- 
--   reflexive : Dummy._≡_ ⇒ _≈_
--   reflexive Dummy.refl = refl
-- 
-- open Dummy public
