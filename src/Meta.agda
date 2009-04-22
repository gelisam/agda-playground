-- modelling W-types using W-types
module Meta (α : Set) (⟦_⟧' : α → Set) where

open import Data.Product
open import Data.Empty
open import Data.Unit
open import Data.Function
open import W


W' : Set
W' = W ⊤ ⟦_⟧ where
  ⟦_⟧ : ⊤ → Set
  ⟦ tt ⟧ = (a : α) → ⟦ a ⟧'

sup' : (a : α) → (f : ⟦ a ⟧' → W') → W'
sup' a f = sup tt λ g → f (g a)
