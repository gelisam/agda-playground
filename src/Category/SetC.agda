module Category.SetC where

open import Category


Set# : Cat
Set# = record
     { #      = Set
     ; _[_⇾_] = λ A B → A → B
     }
