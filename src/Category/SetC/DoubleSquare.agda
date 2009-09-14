module Category.SetC.DoubleSquare where

open import Data.Sum
open import Data.Product

open import Category.SetC
open import Functor
open import Adjunction


Double : Functor Set# Set#
Double = record
       { tmap = λ A → A ⊎ A
       ; fmap = λ f → Data.Sum.map f f
       }

Square : Functor Set# Set#
Square = record
       { tmap = λ A → A × A
       ; fmap = λ f → Data.Product.map f f
       }

Double⊣Square : Double ⊣ Square
Double⊣Square {A} {B} = left , right where
  left : (A ⊎ A → B) → A → B × B
  left f a = f (inj₁ a)
           , f (inj₂ a)
  
  right : (A → B × B) → A ⊎ A → B
  right f (inj₁ a) = proj₁ (f a)
  right f (inj₂ a) = proj₂ (f a)
