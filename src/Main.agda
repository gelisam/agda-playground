module Main where

-- following Conor McBride's "Clowns to the Left of me, Jokers to the Right" paper from POPL 2007.

open import Category.Functor
open import Data.Sum
open import Data.Product


K₁ : (a : Set) → RawFunctor (λ x → a)
K₁ a = record {_<$>_ = _<$>_} where
  _<$>_ : ∀ {s t} → (s → t) → a → a
  f <$> x = x

Id : RawFunctor (λ x → x)
Id = record {_<$>_ = _<$>_} where
  _<$>_ : ∀ {s t} → (s → t) → s → t
  f <$> x = f x

_+₁_ : ∀ {p q} → RawFunctor p → RawFunctor q → RawFunctor (λ x → p x ⊎ q x)
_+₁_ {p} {q} fp fq = record {_<$>_ = _<$>_} where
  _<p>_ : ∀ {s t} → (s → t) → p s → p t
  _<p>_ = RawFunctor._<$>_ fp
  
  _<q>_ : ∀ {s t} → (s → t) → q s → q t
  _<q>_ = RawFunctor._<$>_ fq
  
  _<$>_ : ∀ {s t} → (s → t) → p s ⊎ q s → p t ⊎ q t
  f <$> (inj₁ x) = inj₁ (f <p> x)
  f <$> (inj₂ y) = inj₂ (f <q> y)

_×₁_ : ∀ {p q} → RawFunctor p → RawFunctor q → RawFunctor (λ x → p x × q x)
_×₁_ {p} {q} fp fq = record {_<$>_ = _<$>_} where
  _<p>_ : ∀ {s t} → (s → t) → p s → p t
  _<p>_ = RawFunctor._<$>_ fp
  
  _<q>_ : ∀ {s t} → (s → t) → q s → q t
  _<q>_ = RawFunctor._<$>_ fq
  
  _<$>_ : ∀ {s t} → (s → t) → p s × q s → p t × q t
  f <$> (x , y) = (f <p> x , f <q> y)


-- negative occurence, damn!
data Rec {f : Set → Set}(p : RawFunctor f) : Set where
  μ : f (Rec p) → Rec p
