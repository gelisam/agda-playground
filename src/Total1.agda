module Total1 where

open import Relation.Binary.PropositionalEquality1


data Compare₁ {A : Set₁} : A → A → Set₁ where
  lt : ∀ x y → Compare₁ x y
  eq : ∀  x  → Compare₁ x x
  gt : ∀ x y → Compare₁ x y

uncompare₁ : ∀ {A x y}
           → Compare₁ {A} x y
           → Compare₁ {A} y x
uncompare₁ (lt x y) = gt y x
uncompare₁ (eq  x ) = eq  x
uncompare₁ (gt x y) = lt y x

record Total₁ (A : Set₁) : Set₁ where
  field
    compare : (x y : A) → Compare₁ x y
    valid   : (x y : A)
            → compare x y ≡₁ uncompare₁ (compare y x)
