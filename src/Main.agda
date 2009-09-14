module Main where

open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.Function
open import Relation.Nullary

record Cat : Set2 where
  field
    #      : Set1
    _[_⇾_] : # → # → Set
open Cat

record Functor (A# B# : Cat) : Set1 where
  field
    tmap : # A# → # B#
    fmap : {A₁ A₂ : # A#}
         → A# [      A₁ ⇾      A₂ ]
         → B# [ tmap A₁ ⇾ tmap A₂ ]
open Functor

infix 1 _⋅_
_⋅_ : ∀ {A# B#}
    → (F : Functor A# B#)
    → # A#
    → # B#
_⋅_ = tmap

infix 0 _⊣_
_⊣_ : ∀ {A# B#}
    → (F : Functor A# B#)
    → (G : Functor B# A#)
    → Set1
_⊣_ {A#} {B#} F G = ∀ {A B}
                  → B# [ F ⋅ A ⇾     B ]
                  ⇔ A# [     A ⇾ G ⋅ B ]


Set# : Cat
Set# = record
     { #      = Set
     ; _[_⇾_] = λ A B → A → B
     }

Double : Functor Set# Set#
Double = record
       { tmap = λ A → A ⊎ A
       ; fmap = λ f → Data.Sum.map f f
       }

Square : Functor Set# Set#
Square = record
       { tmap = λ A → A × A
       ; fmap = λ f → Data.Product.map f f
       }

Double⊣Square : Double ⊣ Square
Double⊣Square {A} {B} = left , right where
  left : (A ⊎ A → B) → A → B × B
  left f a = f (inj₁ a)
           , f (inj₂ a)
  
  right : (A → B × B) → A ⊎ A → B
  right f (inj₁ a) = proj₁ (f a)
  right f (inj₂ a) = proj₂ (f a)

-- Containers
infix 2 _◃_
_◃_ : (S P : Set)
    → Functor Set# Set#
_◃_ S P = record
        { tmap = λ A → S × (P → A)
        ; fmap = λ f x → proj₁ x , f ∘ proj₂ x
        }

◃⊤⊣⊤◃ : ∀ {X}
      → X ◃ ⊤
      ⊣ ⊤ ◃ X
◃⊤⊣⊤◃ {X} {A} {B} = left , right where
  left : (X ◃ ⊤ ⋅ A → B) → A → ⊤ ◃ X ⋅ B
  left f a = tt , λ x → f (x , λ tt → a)
  
  right : (A → ⊤ ◃ X ⋅ B) → X ◃ ⊤ ⋅ A → B
  right f (x , const-a) = proj₂ (f (const-a tt)) x

And : (X : Set)
    → Functor Set# Set#
And X = record
      { tmap = λ A → X × A
      ; fmap = λ f x → proj₁ x , f (proj₂ x)
      }

Arr : (X : Set)
    → Functor Set# Set#
Arr X = record
      { tmap = λ A → X → A
      ; fmap = λ f x → f ∘ x
      }

And⊣Arr : ∀ {X}
        → And X ⊣ Arr X
And⊣Arr {X} {A} {B} = left , right where
  left : (And X ⋅ A → B) → A → Arr X ⋅ B
  left f a = λ x → f (x , a)
  
  right : (A → Arr X ⋅ B) → And X ⋅ A → B
  right f (x , a) = f a x


Quantifier# : Set → Cat
Quantifier# W = record
              { #      = W → Set
              ; _[_⇾_] = λ A B → (w : W) → A w → B w
              }
