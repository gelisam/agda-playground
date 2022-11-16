module Main where

open import Data.Empty
open import Data.Nat
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

eq-dec-succ
  : (x y : ℕ)
  → Dec (x ≡ y)
  → Dec (suc x ≡ suc y)
eq-dec-succ x .x (yes refl)
  = yes refl
eq-dec-succ x y (no x≢y)
  = no (go x y x≢y)
  where
    go : (x y : ℕ) → ¬ (x ≡ y) → suc x ≡ suc y → ⊥
    go x .x x≢y refl = x≢y refl

eq-dec
  : (x y : ℕ)
  → Dec (x ≡ y)
eq-dec zero zero
  = yes refl
eq-dec zero (suc _)
  = no λ()
eq-dec (suc _) zero
  = no λ()
eq-dec (suc x) (suc y)
  = eq-dec-succ x y (eq-dec x y)
