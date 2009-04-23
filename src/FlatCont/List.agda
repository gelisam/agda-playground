module FlatCont.List (α : Set) where

open import FlatCont

-- FlatCont is not strong enough to model lists.
-- Actually, (FlatCont List ⊤ ⊤) works, but then
-- FlatCont is rather useless.
