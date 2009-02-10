{-# OPTIONS --sized-types #-}
module Main where

open import Size
open import Data.Unit
open import Data.Sum

-- the many uses of sized types

data N : {i : Size} → Set where
  z : {i : Size} → N {↑ i}
  s : {i : Size} → N {i} → N {↑ i}

case : {i : Size} → N {↑ i} → ⊤ ⊎ N {i}
case z = inj₁ tt
case (s x) = inj₂ x

pass : {i : Size} → N {i} → ⊤
pass .{↑ i} (z {i}) with case {i} (z {i})
... | {- z -}   inj₁ _ = tt
... | {- s y -} inj₂ y = pass {i} y
pass .{↑ i} (s {i} x) with case {i} (s {i} x)
... | {- z -}   inj₁ _ = tt
... | {- s y -} inj₂ y = pass {i} y

short : {i : Size} → N {i} → ⊤
short (z {i}) with case {i} z
... | {- z -}   inj₁ _ = tt
... | {- s y -} inj₂ y = fail y
short (s {i} x) with case {i} (s x)
... | {- z -}   inj₁ _ = tt
... | {- s y -} inj₂ y = short y
