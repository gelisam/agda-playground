module Category where


record Cat : Set2 where
  field
    #      : Set1         -- objects
    _[_⇾_] : # → # → Set  -- morphisms
open Cat public
