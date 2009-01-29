{-# OPTIONS --no-positivity-check #-}
module Main where

open import Data.Empty

-- also try with "codata": it yields exactly the same contradiction.
data Curry↯ : Set where
  ⌈_⌉ : (Curry↯ → ⊥) → Curry↯

⌊_⌋ : Curry↯ → (Curry↯ → ⊥)
⌊_⌋ ⌈ f ⌉ = f

-- the famous looping λ expression (λf. f f)(λf. f f), expressed in agda:
-- δ f = f f
-- ω = δ δ

-- the curry paradox (C = C → ⊥) can be written in the same form.
-- ⌈_⌉ and ⌊_⌋ convert between C and C → ⊥
δ : Curry↯ → ⊥
δ ⌈ f ⌉ = f ⌈ f ⌉
ω : ⊥
ω = δ ⌈ δ ⌉
