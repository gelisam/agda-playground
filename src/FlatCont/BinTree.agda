module FlatCont.BinTree (α : Set) where

open import FlatCont

-- FlatCont is not strong enough to model BinTree.
-- Actually, (FlatCont BinTree ⊤ ⊤) works, but then
-- FlatCont is rather useless.
