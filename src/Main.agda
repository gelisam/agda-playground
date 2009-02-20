module Main where

-- following Conor McBride's "Clowns to the Left of me, Jokers to the Right" paper from POPL 2007.

open import Data.Sum
open import Data.Product


infix 4 _+₁_
infix 4 _×₁_
data Functor₁ : Set1 where
  K    : (α : Set)
       → Functor₁
  Id   : Functor₁
  _+₁_ : (p q : Functor₁)
       → Functor₁
  _×₁_ : (p q : Functor₁)
       → Functor₁

infix 3 _⋅_
_⋅_ : Functor₁ → Set → Set
K α    ⋅ x = α
Id     ⋅ x = x
p +₁ q ⋅ x = p ⋅ x ⊎ q ⋅ x
p ×₁ q ⋅ x = p ⋅ x × q ⋅ x

data Rec (f : Functor₁) : Set where
  μ : f ⋅ (Rec f) → Rec f

fmap : ∀ {f s t} → (s → t) → f ⋅ s → f ⋅ t
fmap {K a}    f x = x
fmap {Id}     f x = f x
fmap {p +₁ q} f (inj₁ x) = inj₁ (fmap {p} f x)
fmap {p +₁ q} f (inj₂ x) = inj₂ (fmap {q} f x)
fmap {p ×₁ q} f (x , y)  = (fmap {p} f x , fmap {q} f y)
