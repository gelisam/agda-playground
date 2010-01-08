module Refl where

open import Relation.Binary.PropositionalEquality public

open import Total


total-≡ : ∀ {A} {x y : A} → Total (x ≡ y)
total-≡ {A} {x} {y} = record
                    { compare = compare
                    ; valid   = valid
                    } where
  compare : (xx yy : x ≡ y) → Compare xx yy
  compare _ _ with x | y
  compare refl refl | .x | x = eq refl
  
  valid : (xx yy : x ≡ y) → compare xx yy ≡ uncompare (compare yy xx)
  valid _ _ with x | y
  valid refl refl | .x | x = refl

≡-always-≡ : ∀ {A} {x y : A} {p q : x ≡ y} → p ≡ q
≡-always-≡ {A} {.x} {x} {refl} {refl} = refl
