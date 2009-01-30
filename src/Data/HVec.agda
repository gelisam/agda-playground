module Data.HVec where
open import Data.Nat
open import Data.Fin
open import Data.Vec1

data HVec : (n : ℕ) → Vec₁ Set n → Set1 where
  []  : HVec 0 []
  _∷_ : ∀ {n α}{Δ : Vec₁ Set n} → α → HVec n Δ → HVec (suc n) (α ∷ Δ)

hlookup : ∀ {n αs}(i : Fin n) → HVec n αs → lookup i αs
hlookup {zero } ()      []
hlookup {suc n} zero    (x ∷ xs) = x
hlookup {suc n} (suc i) (x ∷ xs) = hlookup {n} i xs
