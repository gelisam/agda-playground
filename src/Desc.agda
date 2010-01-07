module Desc where

open import Coinduction

open import Total


data PlainDesc : Set1 where
  arg : ∀ A → Total A → (A → PlainDesc) → PlainDesc
  ret :                                   PlainDesc

data DelayDesc : Set1 where
  arg : ∀ A → Total A → (A → ∞₁ DelayDesc) → DelayDesc
  ret :                                      DelayDesc

data ⟦_⟧ : DelayDesc → Set1 where
  arg : ∀ {A tA d} a → ⟦ ♭₁ (d a) ⟧ → ⟦ arg A tA d ⟧
  ret :                               ⟦ ret ⟧
