module Main where

open import Data.Product

open import Refl
open import Unit
open import Total
open import Lexicographic


data PlainDesc : Set₁ where
  arg : ∀ A → Total A → (A → PlainDesc) → PlainDesc
  rec : PlainDesc →                       PlainDesc
  ret :                                   PlainDesc

⟦_⟧ : PlainDesc → Set → Set
⟦ arg A tA d ⟧ R = ∃ λ a → ⟦ d a ⟧ R
⟦ rec      d ⟧ R = R × ⟦ d ⟧ R
⟦ ret        ⟧ R = ⊤

data PlainData (d : PlainDesc) : Set where
  ⟨_⟩ : ⟦ d ⟧ (PlainData d) → PlainData d


total-⟦_⟧ : ∀ d R → Total R → Total (⟦ d ⟧ R)
total-⟦ arg A tA d ⟧ R tR = lexicographic tA λ a → total-⟦ d a ⟧ R tR
total-⟦ rec      d ⟧ R tR = lexicographic tR λ _ → total-⟦ d   ⟧ R tR
total-⟦ ret        ⟧ R tR = total-⊤


data &Tag : Set where
  eq : &Tag
  lt : &Tag

total-&Tag : Total &Tag
total-&Tag = record
           { compare = compare
           ; valid   = valid
           } where
  compare : (x y : &Tag) → Compare x y
  compare eq eq = eq _
  compare eq lt = lt _ _
  compare lt eq = gt _ _
  compare lt lt = eq _
  
  valid : (x y : &Tag) → compare x y ≡ uncompare (compare y x)
  valid eq eq = refl
  valid eq lt = refl
  valid lt eq = refl
  valid lt lt = refl

& : PlainDesc → PlainDesc
& (arg A tA d) = arg &Tag total-&Tag case-tag where
  case-tag : &Tag → PlainDesc
  case-tag eq = arg A tA λ a
              → & (d a)
  case-tag lt = arg A tA λ x
              → arg A tA λ y
              → arg (Total.compare tA x y ≡ lt x y) total-≡ λ _
              → _
& (rec      d) = _
& (ret       ) = _
