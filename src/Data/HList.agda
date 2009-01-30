module Data.HList where
open import Data.List1

data HList : List₁ Set → Set1 where
  []  : HList []
  _∷_ : ∀ {α Δ} → (x  : α) → (xs : HList Δ) → HList (α ∷ Δ)
