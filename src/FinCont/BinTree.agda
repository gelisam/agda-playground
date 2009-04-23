module FinCont.BinTree (α : Set) where

open import Data.Nat
open import Data.Fin renaming (_+_ to _+F_)
open import FinCont
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- with FinCont, the encoding is complicated
-- by the transformation to and from ℕ, but it is possible

data BinTree0 : Set where
  leaf0 : BinTree0
  node0 : BinTree0
        → BinTree0
        → BinTree0

count : BinTree0 → ℕ
count leaf0 = 1
count (node0 L R) = count L + count R

BinTree : Set
BinTree = FinCont BinTree0 count α

leaf : α → BinTree
leaf x = leaf0 ▹ child where
  child : Fin (count leaf0) → α
  child zero = x
  child (suc ())


data Hilo (n m : ℕ) : Set where
  less : Fin n → Hilo n m
  geq  : Fin m → Hilo n m

postulate hilo : ∀ {n m} → Fin (n + m) → Hilo n m

node : BinTree → BinTree → BinTree
node (xL ▹ childL) (xR ▹ childR) = node0 xL xR ▹ child where
  child : Fin (count (node0 xL xR)) → α
  child p with hilo {count xL} {count xR} p
  ... | less i = childL i
  ... | geq  i = childR i
