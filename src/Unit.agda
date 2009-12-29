module Unit where

open import Relation.Binary.PropositionalEquality

open import Total


data ⊤ : Set where
  tt : ⊤

total-⊤ : Total ⊤
total-⊤ = record
        { compare = compare
        ; valid   = valid
        } where
  compare : (x y : ⊤) → Compare x y
  compare tt tt = eq tt
  
  valid : (x y : ⊤)
        → compare x y ≡ uncompare (compare y x)
  valid tt tt = refl
