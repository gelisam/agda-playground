module Data.Pat where
open import Data.Fun
open import Data.List1
open import Data.HList
open import Data.Product1
open import Data.Product1.Exists

Pat : Set → Set1
Pat β = ∃₁₁ λ αs → Fun αs β

pat-dom : ∀ {α} → Pat α → List₁ Set
pat-dom p = proj₁₁₁ p

pat-apply : ∀ {α}(p : Pat α) → HList (pat-dom p) → α
pat-apply p xs = fun-apply (proj₁₁₂ p) xs
