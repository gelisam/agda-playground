module Adjunction where

open import Data.Function

open import Category
open import Functor


record Adj (A# B# : Cat) : Set1 where
  field
    F   : Functor A# B#
    G   : Functor B# A#
    F⊣G : ∀ {A} {B}
        → B# [ F ⋅ A ⇾     B ]
        → A# [     A ⇾ G ⋅ B ]
    G⊢F : ∀ {A} {B}
        → A# [     A ⇾ G ⋅ B ]
        → B# [ F ⋅ A ⇾     B ]

infixr 2 _⊣∘⊣_
_⊣∘⊣_ : ∀ {A# B# C#}
      → Adj B# C#
      → Adj A# B#
      → Adj A# C#
_⊣∘⊣_ FG XY = let open Adj FG in
              let open Adj XY renaming
                     ( F   to X
                     ; G   to Y
                     ; F⊣G to X⊣Y
                     ; G⊢F to Y⊢X
                     ) in record
            { F   = F ⋅∘⋅ X
            ; G   = Y ⋅∘⋅ G
            ; F⊣G = X⊣Y ∘ F⊣G
            ; G⊢F = G⊢F ∘ Y⊢X
            }

data Indeed {A# B# : Cat}
            (F : Functor A# B#)
            (G : Functor B# A#)
          : Functor A# B#
          → Functor B# A#
          → Set
          where
  indeed : Indeed F G F G

-- type annotation, to make sure a composition yields the
-- functor you think
adjunction_⊣_defined-by : ∀ {A# B#}
                        → (F : Functor A# B#)
                        → (G : Functor B# A#)
                        → (FG : Adj A# B#)
                        → Indeed F G (Adj.F FG) (Adj.G FG)
                        → Adj A# B#
adjunction .(Adj.F FG) ⊣ .(Adj.G FG) defined-by FG indeed = FG
