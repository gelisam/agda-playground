module Functor where

open import Data.Function

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


-- functor composition
infix 2 _⋅∘⋅_
_⋅∘⋅_ : {A# B# C# : Cat}
      → Functor B# C#
      → Functor A# B#
      → Functor A# C#
_⋅∘⋅_ F G = record
          { tmap = λ A → F ⋅ (G ⋅ A)
          ; fmap = fmap F ∘ fmap G
          }
