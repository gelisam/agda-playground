module Main where

open import Data.Unit
open import Data.Sum
open import Data.Product
open import Relation.Nullary


infix 0 _⊣_
_⊣_ : (F G : Set → Set)
           → Set1
F ⊣ G = ∀ {A B}
      → (F A → B)
      ⇔ (A → G B)

⊎⊣× : (λ A → A ⊎ A)
    ⊣ (λ A → A × A)
⊎⊣× {A} {B} = left , right where
  left : (A ⊎ A → B) → A → B × B
  left f a = f (inj₁ a)
           , f (inj₂ a)
  
  right : (A → B × B) → A ⊎ A → B
  right f (inj₁ a) = proj₁ (f a)
  right f (inj₂ a) = proj₂ (f a)

-- Containers
infix 1 _◃_
_◃_ : (S P A : Set)
    → Set
_◃_ S P A = S × (P → A)

◃⊤⊣⊤◃ : ∀ {X}
      → X ◃ ⊤
      ⊣ ⊤ ◃ X
◃⊤⊣⊤◃ {X} {A} {B} = left , right where
  left : (_◃_ X ⊤ A → B) → A → _◃_ ⊤ X B
  left f a = tt , λ x → f (x , λ tt → a)
  
  right : (A → _◃_ ⊤ X B) → _◃_ X ⊤ A → B
  right f (x , const-a) = proj₂ (f (const-a tt)) x
