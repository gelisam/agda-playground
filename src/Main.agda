{-# OPTIONS --sized-types #-}
module Main where

open import Size
open import Data.Unit
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
