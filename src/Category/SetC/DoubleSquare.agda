module Category.SetC.DoubleSquare where

open import Data.Sum
open import Data.Product
open import Data.Product1
open import Data.Function

open import Category
open import Category.SetC
open import Functor
open import Adjunction


_² : Cat → Cat
A# ² = record
     { #      = # A# ×₁₁ # A#
     ; _[_⇾_] = λ A B
              → A# [ proj₁₁₁ A ⇾ proj₁₁₁ B ]
              × A# [ proj₁₁₂ A ⇾ proj₁₁₂ B ]
     }

Δ : ∀ {A#}
  → Functor A# (A# ²)
Δ {A#} = record
       { tmap = λ A → A , A
       ; fmap = λ f → f , f
       }


Either : Functor (Set# ²) Set#
Either = record
       { tmap = λ A
              → proj₁₁₁ A
              ⊎ proj₁₁₂ A
       ; fmap = λ f → Data.Sum.map (proj₁ f) (proj₂ f)
       }

infixr 1 _⋅⊎⋅_
_⋅⊎⋅_ : # Set#
      → # Set#
      → # Set#
A ⋅⊎⋅ B = Either ⋅ (A , B)

Either⊣Δ : Adj (Set# ²) Set#
Either⊣Δ = record
         { F   = Either
         ; G   = Δ
         ; F⊣G = λ {A B} → left  {proj₁₁₁ A} {proj₁₁₂ A} {B}
         ; G⊢F = λ {A B} → right {proj₁₁₁ A} {proj₁₁₂ A} {B}
         } where
  left : ∀ {A₁ A₂ B}
       → (A₁ ⊎ A₂ → B)
       → (A₁ → B) × (A₂ → B)
  left f = f ∘ inj₁
         , f ∘ inj₂
  
  right : ∀ {A₁ A₂ B}
        → (A₁ → B) × (A₂ → B)
        → A₁ ⊎ A₂ → B
  right (f₁ , f₂) (inj₁ a) = f₁ a
  right (f₁ , f₂) (inj₂ a) = f₂ a


Times : Functor (Set# ²) Set#
Times = record
      { tmap = λ A
             → proj₁₁₁ A
             × proj₁₁₂ A
      ; fmap = λ f → Data.Product.map (proj₁ f) (proj₂ f)
      }

infixr 2 _⋅×⋅_
_⋅×⋅_ : # Set#
      → # Set#
      → # Set#
A ⋅×⋅ B = Times ⋅ (A , B)

Δ⊣Times : Adj Set# (Set# ²)
Δ⊣Times = record
        { F   = Δ
        ; G   = Times
        ; F⊣G = λ {A B} → left  {A} {proj₁₁₁ B} {proj₁₁₂ B}
        ; G⊢F = λ {A B} → right {A} {proj₁₁₁ B} {proj₁₁₂ B}
        } where
  left : ∀ {A B₁ B₂}
       → (A → B₁) × (A → B₂) → A → B₁ × B₂
  left (f₁ , f₂) a = f₁ a
                   , f₂ a
  
  right : ∀ {A B₁ B₂}
        → (A → B₁ × B₂) → (A → B₁) × (A → B₂)
  right f = proj₁ ∘ f
          , proj₂ ∘ f


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

Double⊣Square : Adj Set# Set#
Double⊣Square = adjunction Double ⊣ Square
                defined-by (Either⊣Δ ⊣∘⊣ Δ⊣Times)
                indeed
