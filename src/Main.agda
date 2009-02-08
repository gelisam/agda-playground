{-# OPTIONS --sized-types #-}
module Main where

open import Size
open import Data.Unit
open import Data.Sum
import Examples.Closed
import Examples.Open

-- the many uses of sized types

data N : {i : Size} → Set where
  z : {i : Size} → N {↑ i}
  s : {i : Size} → N {i} → N {↑ i}

fail1 : N → ⊤
fail1 x = fail1 x

pass1 : N → ⊤
pass1 z = tt
pass1 (s x) = pass1 x

-- observing that a transformation doesn't increase the size

id2 : N → N
id2 x = x

fail2 : {i : Size} → N {i} → ⊤
fail2 z = tt
fail2 (s x) = fail2 (id2 x)

id3 : {i : Size} → N {i} → N {i}
id3 x = x

fail3 : N → ⊤
fail3 z = tt
fail3 (s x) = fail3 (id3 x)

pass3 : {i : Size} → N {i} → ⊤
pass3 z = tt
pass3 (s x) = pass3 (id3 x)

-- observing that a transformation decreases the size

pred4 : N → ⊤ ⊎ N
pred4 z = inj₁ tt
pred4 (s x) = inj₂ x

fail4 : {i : Size} → N {i} → ⊤
fail4 z = tt
fail4 (s x) with pred4 x
... | inj₁ y = tt
... | inj₂ y = fail4 y

pred5 : {i : Size} → N {↑ ↑ i} → ⊤ ⊎ N {↑ i}
pred5 z = inj₁ tt
pred5 (s x) = inj₂ x

fail5 : {i : Size} → N {i} → ⊤
fail5 z = tt
fail5 (s x) with pred5 x
... | inj₁ y = tt
... | inj₂ y = fail5 y

