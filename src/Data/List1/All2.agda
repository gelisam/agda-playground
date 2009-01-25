module Data.List1.All2 where
open import Data.List1

infixr 5 _∷_
data All₁₂ {α : Set1} (P : α → Set2) : List₁ α → Set2 where 
  []  : All₁₂ P []

  _∷_ : ∀ {x xs}
      → P x
      → All₁₂ P      xs
      → All₁₂ P (x ∷ xs) 
