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

-- doesn't pass termination checking, but compiles
pass : {i : Size} → N {-i-} → ⊤
pass x with case x
... | {- z -}   inj₁ _ = tt
... | {- s y -} inj₂ y = pass y

-- should pass termination checking, but crashes:
--   An internal error has occurred. Please report this as a bug.
--   Location of the error: src/full/Agda/TypeChecking/Constraints.hs:103
fail : {i : Size} → N {i} → ⊤
fail x with case x
... | {- z -}   inj₁ _ = tt
... | {- s y -} inj₂ y = fail y
