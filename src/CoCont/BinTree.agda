module CoCont.BinTree (α : Set) where

open import Data.Unit
open import CoCont

data BinTree0 : Set where
  leaf0 : BinTree0
  node0 : BinTree0
        → BinTree0
        → BinTree0

data Leaves : BinTree0 → Set where
  leafL : α
        → Leaves leaf0
  nodeL : ∀ {L R}
        → Leaves L
        → Leaves R
        → Leaves (node0 L R)

BinTree : Set
BinTree = CoCont BinTree0 Leaves ⊤

leaf : α → BinTree
leaf x = leaf0 ▹ child where
  child : ⊤ → Leaves leaf0
  child tt = leafL x

node : BinTree → BinTree → BinTree
node (xL ▹ childL) (xR ▹ childR) = node0 xL xR ▹ child where
  child : ⊤ → Leaves (node0 xL xR)
  child tt = nodeL (childL tt)
                   (childR tt)
