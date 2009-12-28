module Main where

open import Data.Unit
open import Data.Product

open import Relation.Binary hiding (Total)
open import Relation.Binary.PropositionalEquality


record Total (A : Set) : Set₁ where
  field
    _<_     : Rel A
    compare : Trichotomous _≡_ _<_

data PlainDesc : Set₁ where
  arg : (A : Set) → Total A → (A → PlainDesc) → PlainDesc
  rec : PlainDesc →                             PlainDesc
  ret :                                         PlainDesc

⟦_⟧ : PlainDesc → Set → Set
⟦ arg A tA d ⟧ R = ∃ λ a → ⟦ d a ⟧ R
⟦ rec      d ⟧ R = R × ⟦ d ⟧ R
⟦ ret        ⟧ R = ⊤

data PlainData (d : PlainDesc) : Set where
  ⟨_⟩ : ⟦ d ⟧ (PlainData d) → PlainData d
