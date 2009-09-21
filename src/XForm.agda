module XForm where

open import Category
open import Functor


-- natural transformation
XForm : {A# B# : Cat}
      → (F G : Functor A# B#)
      → Set1
XForm {A#} {B#} F G = (A : # A#)
                    → B# [ F ⋅ A ⇾ G ⋅ A ]
