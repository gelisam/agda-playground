module Main where

open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.Function
open import Relation.Nullary

record Cat : Set2 where
  field
    #      : Set1         -- objects
    _[_⇾_] : # → # → Set  -- morphisms
open Cat

record Functor (A# B# : Cat) : Set1 where
  field
    tmap : # A# → # B#
    fmap : {A₁ A₂ : # A#}
         → A# [      A₁ ⇾      A₂ ]
         → B# [ tmap A₁ ⇾ tmap A₂ ]
open Functor

-- syntactic sugar
infix 1 _⋅_
_⋅_ : ∀ {A# B#}
    → (F : Functor A# B#)
    → # A#
    → # B#
_⋅_ = tmap

-- adjunctions
infix 0 _⊣_
_⊣_ : ∀ {A# B#}
    → (F : Functor A# B#)
    → (G : Functor B# A#)
    → Set1
_⊣_ {A#} {B#} F G = ∀ {A B}
                  → B# [ F ⋅ A ⇾     B ]
                  ⇔ A# [     A ⇾ G ⋅ B ]


-- examples in the category of sets

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

-- containers
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


-- examples in the category of predicates

Pred# : Set → Cat
Pred# W = record
        { #      = W → Set
        ; _[_⇾_] = λ A B → (w : W) → A w → B w
        }

Exists : (W : Set)
       → Functor (Pred# W) Set#
Exists W = record
         { tmap = λ A → Σ W A
         ; fmap = λ f x → proj₁ x , f (proj₁ x) (proj₂ x)
         }

Forall : (W : Set)
       → Functor (Pred# W) Set#
Forall W = record
         { tmap = λ A → (w : W) → A w
         ; fmap = λ f x w → f w (x w)
         }

Weaken : (W : Set)
       → Functor Set# (Pred# W)
Weaken W = record
         { tmap = λ A w → A
         ; fmap = λ f w x → f x
         }
Exists⊣Weaken : {W : Set}
              → Exists W ⊣ Weaken W
Exists⊣Weaken {W} {A} {B} = left , right where
  left : (Σ W A → B) → (w : W) → A w → B
  left f w a = f (w , a)
  
  right : ((w : W) → A w → B) → Σ W A → B
  right f (w , a) = f w a

Weaken⊣Forall : {W : Set}
              → Weaken W ⊣ Forall W
Weaken⊣Forall {W} {A} {B} = left , right where
  left : ((w : W) → A → B w) → A → (w : W) → B w
  left f a w = f w a
  
  right : (A → (w : W) → B w) → (w : W) → A → B w
  right f w a = f a w
