module Cont.BinTree (α : Set) where

open import Data.Product
open import Cont

data BinTree0 : Set where
  leaf0 : BinTree0
  node0 : BinTree0
        → BinTree0
        → BinTree0

data Path : BinTree0 → Set where
  stop   : Path leaf0
  left_  : ∀ {L R}
         → Path L
         → Path (node0 L R)
  right_ : ∀ {L R}
         → Path R
         → Path (node0 L R)

BinTree : Set
BinTree = Cont BinTree0 Path α

leaf : α → BinTree
leaf x = leaf0 ▹ child where
  child : Path leaf0 → α
  child stop = x

node : BinTree → BinTree → BinTree
node (xL ▹ childL) (xR ▹ childR) = node0 xL xR ▹ child where
  child : Path (node0 xL xR) → α
  child (left  p) = childL p
  child (right p) = childR p
