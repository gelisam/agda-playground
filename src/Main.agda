{-# OPTIONS --sized-types #-}
module Main where

open import Size
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Sum
open import Data.Product

-- the many uses of sized types

data SS : Bool → Set where
  z  : SS true
  s  : SS true → SS true
  ∞' : SS false

⇑_ : {b : Bool} → SS b → SS b
⇑_ {true}  x  = s x
⇑_ {false} ∞' = ∞'

S : Set
S = SS true

data N : {i : Size} → Set where
  z : {i : Size} → N {↑ i}
  s : {i : Size} → N {i} → N {↑ i}

data M : {b : Bool}{i : SS b} → Set where
  z : {b : Bool}{i : SS b} → M {b} {⇑ i}
  s : {b : Bool}{i : SS b} → M {b} {i} → M {b} {⇑ i}

case-n : {i : Size}{β : Set} → N {↑ i} → β → (N {i} → β) → β
case-n z     f _ = f
case-n (s x) _ f = f x

-- case-m : {i : S}{β : Set} → M {⇑ i} → β → (M {i} → β) → β
-- case-m z     f _ = f
-- case-m (s x) _ f = f x

case-m : {i : S} → M {true} {⇑ i} →
         {C : Set} → C -> (M {true} {i} -> C) -> C
case-m z     y f = y
case-m (s x) y f = f x

bla-n : {i : Size} → N {i} → ⊤
bla-n .{↑ i} (z {i}) = case-n {i} z tt (bla-n {i})
bla-n .{↑ i} (s {i} x) = case-n {i} (s x) tt (bla-n {i})

bla-m : {i : S} → M {true} {i} → ⊤
bla-m {z} ()
bla-m {s i} x  = case-m {i} x tt (λ y → bla-m y)

case : {i : Size}
     → N {↑ i}
     → {C : Set}
     → C
     → (N {i} → C)
     → C
case z     y f = y
case (s x) y f = f x

bla : {i : S} → M {true} {i} → ⊤
bla {z} ()
bla {s i} x = case-m x tt bla


coerce : {i : S} → M {true} {i} → M {true} {⇑ i}
coerce z = z
coerce (s x) = s (coerce x)

coerce-inf : {i : S} → M {true} {i} → M {false} {∞'}
coerce-inf z = z
coerce-inf (s x) = s (coerce-inf x)

sub : {i : S}{j : SS false} → M {true} {i} → M {false} {j} → M {true} {i}
sub z     n     = z
sub (s m) z     = s m
sub (s m) (s n) = coerce (sub m n)

-- div’ m n computes ceiling(m/(n+1))
div’ : {i : S}{j : SS false} → M {true} {i} → M {false} {j} → M {true} {i}
div’ z     n = z
div’ (s m) n = s (div’ (sub m n) n)

addWith : ((k : Size) → N {k} → N {k})
        → {i j : Size}
        → N {i} → N {j} → N {∞}
addWith f .{↑ i} {j} (z {i}) y = y
addWith f .{↑ i} {j} (s {i} x) y =
  s {∞} (addWith f {j} {i} y (f i x))

addWith-m : ((k : S) → M {true} {k} → M {true} {k})
          → {i j : S}
          → M {true} {i} → M {true} {j} → M {false} {∞'}
addWith-m f .{s i} {j} (z {i = i}) y = coerce-inf y
addWith-m f .{s i} {j} (s {i = i} x) y =
  s (addWith-m f {j} {i} y (f i x))

-- data List (A : Set) : Size → Set where
--   nil  : (i : Size) → List A (↑ i)
--   cons : (i : Size) → A → List A i → List A (↑ i)
-- 
-- data ListM (A : Set) : S → Set where
--   nil  : (i : S) → ListM A (⇑ i)
--   cons : (i : S) → A → ListM A i → ListM A (⇑ i)
-- 
-- L∞ : Set → Set
-- L∞ A = ∃ λ i → ListM A i
-- 
-- coerce-n : ∀ {A i} → List A i → List A (↑ i)
-- coerce-n x = x
-- 
-- coerce-m : ∀ {A i} → ListM A i → ListM A (⇑ i)
-- coerce-m (nil i) = nil (⇑ i)
-- coerce-m (cons i x xs) = cons (⇑ i) x (coerce-m xs)
-- 
-- split : (i : Size)
--       → {A : Set}
--       → (leq : A → A → Bool)
--       → A → List A i → List A i × List A i
-- split .(↑ i) leq a (nil i) = nil i , nil i
-- split .(↑ i) leq a (cons i x xs) with split i leq a xs | leq a x
-- ... | l1 , l2 | true  = coerce-n l1 , cons i x l2
-- ... | l1 , l2 | false = cons i x l1 , coerce-n l2
-- 
-- split-m : (i : S)
--         → {A : Set}
--         → (leq : A → A → Bool)
--         → A → ListM A i → ListM A i × ListM A i
-- split-m .(⇑ i) leq a (nil i) = nil i , nil i
-- split-m .(⇑ i) leq a (cons i x xs) with split-m i leq a xs | leq a x
-- ... | l1 , l2 | true  = coerce-m l1 , cons i x l2
-- ... | l1 , l2 | false = cons i x l1 , coerce-m l2
-- 
-- qsapp : (i : Size)
--       → {A : Set}
--       → (leq : A → A → Bool)
--       → List A i → List A ∞ → List A ∞
-- qsapp .(↑ i) leq (nil i) ys = ys 
-- qsapp .(↑ i) leq (cons i x xs) ys with split i leq x xs
-- ... | l1 , l2 = qsapp i leq l1 (cons ∞ x (qsapp i leq l2 ys))
-- 
-- qsapp-m : (i : S)
--         → {A : Set}
--         → (leq : A → A → Bool)
--         → ListM A i → L∞ A → L∞ A
-- qsapp-m .(⇑ i) leq (nil i) ys = ys
-- qsapp-m .(⇑ i) leq (cons i x xs) ys with split-m i leq x xs
-- ... | l1 , l2 with qsapp-m i leq l2 ys
-- ... | j , s2 = qsapp-m i leq l1 (⇑ j , cons j x s2)
-- 
-- qsort : (i : Size)
--       → {A : Set}
--       → (leq : A → A → Bool)
--       → List A i → List A ∞
-- qsort i leq l1 = qsapp i leq l1 (nil ∞)
-- 
-- qsort-m : (i : S)
--         → {A : Set}
--         → (leq : A → A → Bool)
--         → ListM A i → L∞ A
-- qsort-m i leq l1 = qsapp-m i leq l1 (⇑ z , nil z)

data Tree : {_ : Size} → Set where
  leaf : ∀ {i} → Tree {↑ i}
  node : ∀ {i} → (ℕ → Tree {i}) → Tree {↑ i}

data TreeM : {b : Bool}{i : SS b} → Set where
  leaf : {b : Bool}{i : SS b} → TreeM {b} {⇑ i}
  node : {b : Bool}{i : SS b} → (ℕ → TreeM {b} {i}) → TreeM {b} {⇑ i}

finite-tree : ℕ → Tree {∞}
finite-tree zero = leaf
finite-tree (suc n) = node (λ _ → finite-tree n)

finite-tree-m : ℕ → TreeM {false}
finite-tree-m zero = leaf {false} {∞'}
finite-tree-m (suc n) = node {false} {∞'} (λ _ → finite-tree-m n)

infinite-tree : Tree {∞}
infinite-tree = node finite-tree

infinite-tree-m : TreeM {false}
infinite-tree-m = node {false} {∞'} finite-tree-m

dfs : {i : Size} → Tree {i} → ⊤
dfs leaf = tt  -- found!
dfs (node f) = dfs (f 0)

dfs-m : {i : SS true} → TreeM {_} {i} → ⊤
dfs-m leaf = tt  -- found!
dfs-m (node f) = dfs-m (f 0)
