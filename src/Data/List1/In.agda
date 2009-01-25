module Data.List1.In where
open import Data.List1

infix 4 _∈_
data _∈_ {α : Set1} : α → List₁ α → Set1 where
  here  : ∀ {x}   {xs : List₁ α}                 → x ∈ x ∷ xs
  there : ∀ {x y} {xs : List₁ α} (x∈xs : x ∈ xs) → x ∈ y ∷ xs
