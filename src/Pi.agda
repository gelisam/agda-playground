module Pi where

-- just as cumbersome as Σ;
-- and more importantly, indented the same

Π : (a : Set)
  → (a → Set)
  → Set
Π a f = (x : a)
      → f x
