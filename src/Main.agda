module Main where

open import Data.Product
open import Relation.Binary.PropositionalEquality

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
total-⟦ arg A tA d ⟧ R tR = lexicographic tA (λ a → total-⟦ d a ⟧ R tR)
total-⟦ rec      d ⟧ R tR = lexicographic tR (λ _ → total-⟦ d   ⟧ R tR)
total-⟦ ret        ⟧ R tR = total-⊤
