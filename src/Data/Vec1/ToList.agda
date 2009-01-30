module Data.Vec1.ToList where
open import Data.Vec1
open import Data.List1

toList₁ : ∀ {a n} → Vec₁ a n → List₁ a
toList₁ []       = []
toList₁ (x ∷ xs) = x ∷ toList₁ xs
