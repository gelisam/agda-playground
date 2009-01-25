module Data.HList where
open import Data.List1

data HList : List₁ Set → Set1 where
  []  : HList []

  _∷_ : {α : Set} {Δ : List₁ Set}
      → (x  : α)
      → (xs : HList Δ)
      → HList (α ∷ Δ)
