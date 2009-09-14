module Functor where

open import Category


record Functor (A# B# : Cat) : Set1 where
  field
    tmap : # A# → # B#
    fmap : {A₁ A₂ : # A#}
         → A# [      A₁ ⇾      A₂ ]
         → B# [ tmap A₁ ⇾ tmap A₂ ]
open Functor public

-- syntactic sugar
infix 1 _⋅_
_⋅_ : ∀ {A# B#}
    → (F : Functor A# B#)
    → # A#
    → # B#
_⋅_ = tmap
