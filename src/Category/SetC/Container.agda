module Category.SetC.Container where

open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.Function

open import Category.SetC
open import Functor
open import Adjunction


infix 2 _◃_
_◃_ : (S P : Set)
    → Functor Set# Set#
_◃_ S P = record
        { tmap = λ A → S × (P → A)
        ; fmap = λ f x → proj₁ x , f ∘ proj₂ x
        }

◃⊤⊣⊤◃ : ∀ {X}
      → X ◃ ⊤
      ⊣ ⊤ ◃ X
◃⊤⊣⊤◃ {X} {A} {B} = left , right where
  left : (X ◃ ⊤ ⋅ A → B) → A → ⊤ ◃ X ⋅ B
  left f a = tt , λ x → f (x , λ tt → a)
  
  right : (A → ⊤ ◃ X ⋅ B) → X ◃ ⊤ ⋅ A → B
  right f (x , const-a) = proj₂ (f (const-a tt)) x
