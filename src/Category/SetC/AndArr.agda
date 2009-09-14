module Category.SetC.AndArr where

open import Data.Product
open import Data.Function

open import Category.SetC
open import Functor
open import Adjunction


And : (X : Set)
    → Functor Set# Set#
And X = record
      { tmap = λ A → X × A
      ; fmap = λ f x → proj₁ x , f (proj₂ x)
      }

Arr : (X : Set)
    → Functor Set# Set#
Arr X = record
      { tmap = λ A → X → A
      ; fmap = λ f x → f ∘ x
      }

And⊣Arr : ∀ {X}
        → And X ⊣ Arr X
And⊣Arr {X} {A} {B} = left , right where
  left : (And X ⋅ A → B) → A → Arr X ⋅ B
  left f a = λ x → f (x , a)
  
  right : (A → Arr X ⋅ B) → And X ⋅ A → B
  right f (x , a) = f a x
