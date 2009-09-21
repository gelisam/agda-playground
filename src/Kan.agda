module Kan where

open import Category
open import Functor
open import XForm


record Ran (A# B# C# : Cat)
           (F : Functor A# B#)
           (X : Functor A# C#)
         : Set1
           where
  field
    R : Functor B# C#
    η : XForm (R ⋅∘⋅ F) X
    δ : (R' : Functor B# C#)
      → (η' : XForm (R' ⋅∘⋅ F) X)
      → XForm R' R
open Ran public

record Lan (A# B# C# : Cat)
           (F : Functor A# B#)
           (X : Functor A# C#)
         : Set1
           where
  field
    L : Functor B# C#
    ε : XForm X (L ⋅∘⋅ F)
    σ : (L' : Functor B# C#)
      → (ε' : XForm X (L' ⋅∘⋅ F))
      → XForm L L'
open Lan public
