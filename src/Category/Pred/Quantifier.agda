module Category.Pred.Quantifier where

open import Data.Product

open import Category.SetC
open import Category.Pred
open import Functor
open import Adjunction


-- examples in the category of predicates

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


-- λ A → W × A
And : (W : Set)
    → Functor Set# Set#
And W = Exists W ⋅∘⋅ Weaken W

-- λ A → W → A
Arr : (W : Set)
    → Functor Set# Set#
Arr W = Forall W ⋅∘⋅ Weaken W

And⊣Arr : {W : Set}
        → AndK W ⊣ ArrK W
And⊣Arr {W} = ∘-preserves-⊣ (Exists W) (Weaken W) (Forall W) (Weaken W)
                (λ {A} {B} → Exists⊣Weaken {W} {A} {B})
                (λ {A} {B} → Weaken⊣Forall {W} {A} {B})
