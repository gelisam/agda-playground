module Data.Fun where
open import Data.List1
open import Data.HList

Fun : List₁ Set → Set → Set1
Fun αs β = HList αs → β

fun-apply : {αs : List₁ Set}{β : Set}
          → Fun αs β
          → HList αs
          → β
fun-apply f xs = f xs