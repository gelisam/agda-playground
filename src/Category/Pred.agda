module Category.Pred where

open import Category


Pred# : Set → Cat
Pred# W = record
        { #      = W → Set
        ; _[_⇾_] = λ A B → (w : W) → A w → B w
        }
