-- Example, Binary Trees as an instance of a W-type
module Weak.BinTree where
open import Data.Nat
open import Data.Fin hiding (_+_)

import Weak

⟦_⟧ : Fin 2 → ℕ
⟦ zero     ⟧ = 0
⟦ suc zero ⟧ = 2
⟦ suc (suc ()) ⟧

open Weak (Fin 2) ⟦_⟧


BinTree : Set
BinTree = Weak

leaf : BinTree
leaf = sup (# 0) (childs 0)

node : BinTree → BinTree → BinTree
node l r = sup (# 1) (childs 2 l r)

-- an example tree
example = node (node leaf (node leaf leaf)) leaf

-- a function to count the number of notes (returns ? for example)
numberOfNodes : BinTree → ℕ
numberOfNodes w = wrec {λ w → ℕ} w branches where
  branches : (shape : Fin 2)
           → (child : Fin ⟦ shape ⟧ → BinTree)
           → (child-count : Fin ⟦ shape ⟧ → ℕ)
           → ℕ
  branches zero       child child-count = 1
  branches (suc zero) child child-count = child-count (# 0)
                                        + child-count (# 1)
  branches (suc (suc ())) _ _
