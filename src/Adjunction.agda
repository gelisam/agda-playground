module Adjunction where

open import Data.Product
open import Data.Function
open import Relation.Nullary

open import Category
open import Functor


infix 0 _⊣_
_⊣_ : ∀ {A# B#}
    → (F : Functor A# B#)
    → (G : Functor B# A#)
    → Set1
_⊣_ {A#} {B#} F G = ∀ {A} {B}
                  → B# [ F ⋅ A ⇾     B ]
                  ⇔ A# [     A ⇾ G ⋅ B ]

∘-preserves-⊣ : ∀ {A# L# R#}
              → (F : Functor A# R#)
              → (X : Functor L# A#)
              → (Y : Functor A# L#)
              → (G : Functor R# A#)
              → F       ⊣       G
              →       X ⊣ Y
              → F ⋅∘⋅ X ⊣ Y ⋅∘⋅ G
∘-preserves-⊣ {A#} {L#} {R#} F X Y G F⊣G X⊣Y {L} {R} = left , right where
  left : R# [ F ⋅∘⋅ X ⋅ L ⇾           R ]
       → L# [           L ⇾ Y ⋅∘⋅ G ⋅ R ]
  left = proj₁ X⊣Y ∘ proj₁ F⊣G
  
  right : L# [           L ⇾ Y ⋅∘⋅ G ⋅ R ]
        → R# [ F ⋅∘⋅ X ⋅ L ⇾           R ]
  right = proj₂ F⊣G ∘ proj₂ X⊣Y
