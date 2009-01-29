{-# OPTIONS --no-positivity-check #-}
module Main where

data ⊥ : Set where

-- also try with "codata": it yields exactly the same contradiction.
data Curry↯ : Set where
  ⌈_⌉ : (Curry↯ → ⊥) → Curry↯

⌊_⌋ : Curry↯ → (Curry↯ → ⊥)
⌊_⌋ ⌈ f ⌉ = f

-- the famous looping λ expression (\f. f f)(\f. f f), expressed in agda:
-- loop' f = f f
-- loop = loop' loop'

-- the curry paradox (C = C → ⊥) can be written in the same form.
-- ⌈_⌉ and ⌊_⌋ convert between C and C → ⊥
loop' : Curry↯ → ⊥
loop' ⌈ f ⌉ = f ⌈ f ⌉
loop : ⊥
loop = loop' ⌈ loop' ⌉
