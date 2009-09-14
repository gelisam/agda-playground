module Adjunction where

open import Relation.Nullary

open import Category
open import Functor


infix 0 _⊣_
_⊣_ : ∀ {A# B#}
    → (F : Functor A# B#)
    → (G : Functor B# A#)
    → Set1
_⊣_ {A#} {B#} F G = ∀ {A B}
                  → B# [ F ⋅ A ⇾     B ]
                  ⇔ A# [     A ⇾ G ⋅ B ]
