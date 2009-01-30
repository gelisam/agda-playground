module Data.HList where
open import Data.List1

data HList : List₁ Set → Set1 where
  []  : HList []
  _∷_ : ∀ {α Δ} → α → HList Δ → HList (α ∷ Δ)
