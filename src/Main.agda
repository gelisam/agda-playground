{-# OPTIONS --sized-types #-}
module Main where

open import Size
open import Data.Unit
open import Data.Bool
open import Data.Sum
open import Data.Product

-- the many uses of sized types

data S : Set where
  z : S
  ⇑_ : S → S

data N : {i : Size} → Set where
  z : {i : Size} → N {↑ i}
  s : {i : Size} → N {i} → N {↑ i}

data M : {i : S} → Set where
  z : {i : S} → M {⇑ i}
  s : {i : S} → M {i} → M {⇑ i}

M∞ : Set
M∞ = ∃ λ i → M {i}

case-n : {i : Size}{β : Set} → N {↑ i} → β → (N {i} → β) → β
case-n z     f _ = f
case-n (s x) _ f = f x

-- case-m : {i : S}{β : Set} → M {⇑ i} → β → (M {i} → β) → β
-- case-m z     f _ = f
-- case-m (s x) _ f = f x

case-m : {i : S} → M {⇑ i} →
         {C : Set} → C -> (M {i} -> C) -> C
case-m z     y f = y
case-m (s x) y f = f x

bla-n : {i : Size} → N {i} → ⊤
bla-n .{↑ i} (z {i}) = case-n {i} z tt (bla-n {i})
bla-n .{↑ i} (s {i} x) = case-n {i} (s x) tt (bla-n {i})

bla-m : {i : S} → M {i} → ⊤
bla-m {z} ()
bla-m {⇑ i} x  = case-m x tt (λ y → bla-m y)

case : {i : Size}
     → N {↑ i}
     → {C : Set}
     → C
     → (N {i} → C)
     → C
case z     y f = y
case (s x) y f = f x

bla : {i : S} → M {i} → ⊤
bla {z} ()
bla {⇑ i} x = case-m x tt bla


coerce : {i : S} → M {i} → M {⇑ i}
coerce z = z
coerce (s x) = s (coerce x)

sub : {i : S} → M {i} → M∞ → M {i}
sub z     (_ , n)            = z
sub (s m) (.(⇑ i) , z {i})   = s m
sub (s m) (.(⇑ i) , s {i} n) = coerce (sub m (_ , n))

-- div’ m n computes ceiling(m/(n+1))
div’ : {i : S} → M {i} → M∞ → M {i}
div’ z     n = z
div’ (s m) n = s (div’ (sub m n) n)

addWith : ((k : Size) → N {k} → N {k})
        → {i j : Size}
        → N {i} → N {j} → N {∞}
addWith f .{↑ i} {j} (z {i}) y = y
addWith f .{↑ i} {j} (s {i} x) y =
  s {∞} (addWith f {j} {i} y (f i x))

addWith-m : ((k : S) → M {k} → M {k})
          → {i j : S}
          → M {i} → M {j} → M∞
addWith-m f .{⇑ i} {j} (z {i}) y = _ , y
addWith-m f .{⇑ i} {j} (s {i} x) y = _ ,
  s (proj₂ (addWith-m f {j} {i} y (f i x)))

data List (A : Set) : Size → Set where
  nil  : (i : Size) → List A (↑ i)
  cons : (i : Size) → A → List A i → List A (↑ i)

data ListM (A : Set) : S → Set where
  nil  : (i : S) → ListM A (⇑ i)
  cons : (i : S) → A → ListM A i → ListM A (⇑ i)

L∞ : Set → Set
L∞ A = ∃ λ i → ListM A i

coerce-n : ∀ {A i} → List A i → List A (↑ i)
coerce-n x = x

coerce-m : ∀ {A i} → ListM A i → ListM A (⇑ i)
coerce-m (nil i) = nil (⇑ i)
coerce-m (cons i x xs) = cons (⇑ i) x (coerce-m xs)

split : (i : Size)
      → {A : Set}
      → (leq : A → A → Bool)
      → A → List A i → List A i × List A i
split .(↑ i) leq a (nil i) = nil i , nil i
split .(↑ i) leq a (cons i x xs) with split i leq a xs | leq a x
... | l1 , l2 | true  = coerce-n l1 , cons i x l2
... | l1 , l2 | false = cons i x l1 , coerce-n l2

split-m : (i : S)
        → {A : Set}
        → (leq : A → A → Bool)
        → A → ListM A i → ListM A i × ListM A i
split-m .(⇑ i) leq a (nil i) = nil i , nil i
split-m .(⇑ i) leq a (cons i x xs) with split-m i leq a xs | leq a x
... | l1 , l2 | true  = coerce-m l1 , cons i x l2
... | l1 , l2 | false = cons i x l1 , coerce-m l2

qsapp : (i : Size)
      → {A : Set}
      → (leq : A → A → Bool)
      → List A i → List A ∞ → List A ∞
qsapp .(↑ i) leq (nil i) ys = ys 
qsapp .(↑ i) leq (cons i x xs) ys with split i leq x xs
... | l1 , l2 = qsapp i leq l1 (cons ∞ x (qsapp i leq l2 ys))

qsapp-m : (i : S)
        → {A : Set}
        → (leq : A → A → Bool)
        → ListM A i → L∞ A → L∞ A
qsapp-m .(⇑ i) leq (nil i) ys = ys
qsapp-m .(⇑ i) leq (cons i x xs) ys with split-m i leq x xs
... | l1 , l2 with qsapp-m i leq l2 ys
... | j , s2 = qsapp-m i leq l1 (⇑ j , cons j x s2)

qsort : (i : Size)
      → {A : Set}
      → (leq : A → A → Bool)
      → List A i → List A ∞
qsort i leq l1 = qsapp i leq l1 (nil ∞)

qsort-m : (i : S)
        → {A : Set}
        → (leq : A → A → Bool)
        → ListM A i → L∞ A
qsort-m i leq l1 = qsapp-m i leq l1 (⇑ z , nil z)
