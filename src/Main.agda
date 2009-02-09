module Main where

open import Data.Unit
open import Data.Sum

-- the many uses of sized types

data Size : Set where
  z : Size
  ↑_ : Size → Size

data N : {i : Size} → Set where
  z : {i : Size} → N {↑ i}
  s : {i : Size} → N {i} → N {↑ i}

case : {i : Size} → N {↑ i} → ⊤ ⊎ N {i}
case z = inj₁ tt
case (s x) = inj₂ x

pass : {i : Size} → N {i} → ⊤
pass {z} ()
pass {↑ i} x with case x
... | {- z -}   inj₁ _ = tt
... | {- s y -} inj₂ y = pass y
