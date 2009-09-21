module Category.Rel where

open import Category


record Rel : Set1 where
  field
    A  : Set
    A' : Set
    A~ : A → A' → Set

record Val (R : Rel) : Set where
  open Rel R
  field
    a  : A
    a' : A'
    a~ : A~ a a'

Rel# : Cat
Rel# = record
     { #      = Rel
     ; _[_⇾_] = λ RA RB
              → let open Rel RA in
                let open Rel RB renaming
                       ( A to B
                       ; A' to B'
                       ; A~ to B~
                       ) in
                (ra : Val RA)
              → let open Val ra in
                Val record
              { A  = A  → B
              ; A' = A' → B'
              ; A~ = λ f f'
                   → B~ (f a) (f' a')
              }
     }
