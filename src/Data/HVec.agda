module Data.HVec where
open import Data.Nat
open import Data.Vec1

data HVec : (n : ℕ) → Vec₁ Set n → Set1 where
  []  : HVec 0 []
  _∷_ : ∀ {n α}{Δ : Vec₁ Set n} → α → HVec n Δ → HVec (suc n) (α ∷ Δ)
