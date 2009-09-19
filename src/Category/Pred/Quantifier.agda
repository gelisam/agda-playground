module Category.Pred.Quantifier where

open import Data.Product
open import Data.Function

open import Category.SetC
open import Category.Pred
open import Functor
open import Adjunction


data ⊤ : Set where
  unit : ⊤


Weaken : (W : Set)
       → Functor Set# (Pred# W)
Weaken W = record
         { tmap = λ A w → A
         ; fmap = λ f w x → f x
         }


Exists : (W : Set)
       → Functor (Pred# W) Set#
Exists W = record
         { tmap = λ A → Σ W A
         ; fmap = λ f x → proj₁ x , f (proj₁ x) (proj₂ x)
         }
Exists⊣Weaken : (W : Set)
              → Adj (Pred# W) Set#
Exists⊣Weaken W = record
                { F   = Exists W
                ; G   = Weaken W
                ; F⊣G = curry
                ; G⊢F = uncurry
                }

Weaken⊣Exists : Adj Set# (Pred# ⊤)
Weaken⊣Exists = record
              { F   = Weaken ⊤
              ; G   = Exists ⊤
              ; F⊣G = left
              ; G⊢F = right
              } where
  left : {A : Set}
       → {B : ⊤ → Set}
       → (∀ u → A → B u)
       → A → Σ ⊤ B
  left f a = unit , f unit a
  
  right : {A : Set}
        → {B : ⊤ → Set}
        → (A → Σ ⊤ B)
        → ∀ u → A → B u
  right f unit a with f a
  right f unit a | unit , b = b


Forall : (W : Set)
       → Functor (Pred# W) Set#
Forall W = record
         { tmap = λ A → (w : W) → A w
         ; fmap = λ f x w → f w (x w)
         }

Weaken⊣Forall : (W : Set)
              → Adj Set# (Pred# W)
Weaken⊣Forall W = record
                { F   = Weaken W
                ; G   = Forall W
                ; F⊣G = λ f a w → f w a  -- dependent flip
                ; G⊢F = λ f w a → f a w  -- dependent flip
                }

Forall⊣Weaken : Adj (Pred# ⊤) Set#
Forall⊣Weaken = record
              { F   = Forall ⊤
              ; G   = Weaken ⊤
              ; F⊣G = left
              ; G⊢F = right
              } where
  left : {A : ⊤ → Set}
       → {B : Set}
       → ((∀ u → A u) → B)
       → ∀ u → A u → B
  left {A} f unit a = f Ka where
    Ka : (u : ⊤) → A u
    Ka unit = a
  
  right : {A : ⊤ → Set}
        → {B : Set}
        → (∀ u → A u → B)
        → (∀ u → A u) → B
  right f Ka = f unit (Ka unit)


And : (W : Set)
    → Functor Set# Set#
And W = record
      { tmap = λ A → W × A
      ; fmap = λ f x → proj₁ x , f (proj₂ x)
      }

Arr : (W : Set)
    → Functor Set# Set#
Arr W = record
      { tmap = λ A → W → A
      ; fmap = λ f g → f ∘ g
      }
And⊣Arr : (W : Set)
        → Adj Set# Set#
And⊣Arr W = adjunction And W ⊣ Arr W
            defined-by (Exists⊣Weaken W ⊣∘⊣ Weaken⊣Forall W)
            indeed

-- λ A → ⊤ → A 
-- ⊣ 
-- λ A → ⊤ × A
Arr⊣And : Adj Set# Set#
Arr⊣And = adjunction Arr ⊤ ⊣ And ⊤
          defined-by (Forall⊣Weaken ⊣∘⊣ Weaken⊣Exists)
          indeed

-- Containers with shapes of type S and positions of type P
infix 2 _◃_
_◃_ : (S P : Set)
    → Functor Set# Set#
_◃_ S P = And S ⋅∘⋅ Arr P

◃⊤⊣⊤◃ : (X : Set)
      → Adj Set# Set#
◃⊤⊣⊤◃ X = adjunction X ◃ ⊤ ⊣ ⊤ ◃ X
          defined-by (And⊣Arr X ⊣∘⊣ Arr⊣And)
          indeed
