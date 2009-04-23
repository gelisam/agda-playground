-- an example using the meta W.
-- no overhead as compared to the ordinary W, wow!
module W.W.Nat where

open import Data.Empty
open import Data.Unit
open import Data.Function
import Meta

data Tag : Set where
  Zero : Tag
  Succ : Tag

⟦_⟧ : Tag → Set
⟦ Zero ⟧ = ⊥
⟦ Succ ⟧ = ⊤

open Meta Tag ⟦_⟧

Nat' : Set
Nat' = W'

zero : Nat'
zero = sup' Zero λ()

succ : Nat' → Nat'
succ n = sup' Succ (const n)
