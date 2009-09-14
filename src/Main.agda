module Main where

open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.Function
open import Relation.Nullary

record Cat : Set2 where
  field
    object : Set1
    value  : object → Set

∥_∥ : Cat → Set1
∥_∥ = Cat.object

val : (A# : Cat)
    → ∥ A# ∥
    → Set
val A# A = Cat.value A# A

Set# : Cat
Set# = record
     { object = Set
     ; value  = λ x → x
     }

record Functor (A# B# : Cat) : Set1 where
  field
    tmap : ∥ A# ∥ → ∥ B# ∥
    fmap : {A₁ A₂ : ∥ A# ∥}
         → (val A#       A₁  → val A#       A₂ )
         → (val B# (tmap A₁) → val B# (tmap A₂))

open Functor

infix 1 _⋅_
_⋅_ : ∀ {A# B#}
    → (F : Functor A# B#)
    → ∥ A# ∥
    → ∥ B# ∥
_⋅_ = tmap


infix 0 _⊣_
_⊣_ : ∀ {A# B#}
    → (F : Functor A# B#)
    → (G : Functor B# A#)
    → Set1
_⊣_ {A#} {B#} F G = ∀ {A B}
                  → (val B# (F ⋅ A) → val B#      B )
                  ⇔ (val A#      A  → val A# (G ⋅ B))

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
