module Category.Pred.Quantifier where

open import Data.Product

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
Exists⊣Weaken : {W : Set}
              → Exists W ⊣ Weaken W
Exists⊣Weaken {W} {A} {B} = left , right where
  left : (Σ W A → B) → ∀ w → A w → B
  left f w a = f (w , a)
  
  right : (∀ w → A w → B) → Σ W A → B
  right f (w , a) = f w a

Weaken⊣Exists : Weaken ⊤ ⊣ Exists ⊤
Weaken⊣Exists {A} {B} = left , right where
  left : (∀ u → A → B u) → A → Σ ⊤ B
  left f a = unit , f unit a
  
  right : (A → Σ ⊤ B) → ∀ u → A → B u
  right f unit a with f a
  right f unit a | unit , b = b


Forall : (W : Set)
       → Functor (Pred# W) Set#
Forall W = record
         { tmap = λ A → (w : W) → A w
         ; fmap = λ f x w → f w (x w)
         }

Weaken⊣Forall : {W : Set}
              → Weaken W ⊣ Forall W
Weaken⊣Forall {W} {A} {B} = left , right where
  left : (∀ w → A → B w) → A → ∀ w → B w
  left f a w = f w a
  
  right : (A → ∀ w → B w) → ∀ w → A → B w
  right f w a = f a w

Forall⊣Weaken : Forall ⊤ ⊣ Weaken ⊤
Forall⊣Weaken {A} {B} = left , right where
  left : ((∀ u → A u) → B) → ∀ u → A u → B
  left f unit a = f Ka where
    Ka : (u : ⊤) → A u
    Ka unit = a
  
  right : (∀ u → A u → B) → (∀ u → A u) → B
  right f Ka = f unit (Ka unit)


-- λ A → W × A
And : (W : Set)
    → Functor Set# Set#
And W = Exists W ⋅∘⋅ Weaken W

-- λ A → W → A
Arr : (W : Set)
    → Functor Set# Set#
Arr W = Forall W ⋅∘⋅ Weaken W

And⊣Arr : {W : Set}
        → And W ⊣ Arr W
And⊣Arr {W} = ∘-preserves-⊣ (Exists W) (Weaken W) (Forall W) (Weaken W)
                (λ {A} {B} → Exists⊣Weaken {W} {A} {B})
                (λ {A} {B} → Weaken⊣Forall {W} {A} {B})

Arr⊣And : Forall ⊤ ⋅∘⋅ Weaken ⊤ ⊣ Exists ⊤ ⋅∘⋅ Weaken ⊤
Arr⊣And = ∘-preserves-⊣ (Forall ⊤) (Weaken ⊤) (Exists ⊤) (Weaken ⊤)
            (λ {A} {B} → Forall⊣Weaken {A} {B})
            (λ {A} {B} → Weaken⊣Exists {A} {B})


-- Containers with shapes of type S and positions of type P
infix 2 _◃_
_◃_ : (S P : Set)
    → Functor Set# Set#
_◃_ S P = And S ⋅∘⋅ Arr P

◃⊤⊣⊤◃ : ∀ {X}
      → X ◃ ⊤
      ⊣ ⊤ ◃ X
◃⊤⊣⊤◃ {X} = ∘-preserves-⊣ (And X) (Arr ⊤) (And ⊤) (Arr X)
              (λ {A} {B} → And⊣Arr {X} {A} {B})
              (λ {A} {B} → Arr⊣And     {A} {B})
