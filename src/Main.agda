module Main where

open import Examples.Nat


open import Coinduction

open import Refl
open import Total
open import Desc


-- total-⟦_⟧ : ∀ d → Total ⟦ d ⟧
-- total-⟦ arg A tA d ⟧ = lexicographic tA λ a → total-⟦ d a ⟧
-- total-⟦ ret        ⟧ = total-⊤


-- data &Tag : Set where
--   eq : &Tag
--   lt : &Tag
-- 
-- total-&Tag : Total &Tag
-- total-&Tag = record
--            { compare = compare
--            ; valid   = valid
--            } where
--   compare : (x y : &Tag) → Compare x y
--   compare eq eq = eq _
--   compare eq lt = lt _ _
--   compare lt eq = gt _ _
--   compare lt lt = eq _
--   
--   valid : (x y : &Tag) → compare x y ≡ uncompare (compare y x)
--   valid eq eq = refl
--   valid eq lt = refl
--   valid lt eq = refl
--   valid lt lt = refl
-- 
-- 
-- & : PlainDesc → PlainDesc
-- & (arg A tA d) = arg &Tag total-&Tag case-tag where
--   case-tag : &Tag → PlainDesc
--   case-tag eq = arg A tA λ a
--               → & (d a)
--   case-tag lt = arg A tA λ x
--               → arg A tA λ y
--               → arg (Total.compare tA x y ≡ lt x y) total-≡ λ _
--               → arg ⟦ d x ⟧ total-⟦ d x ⟧ λ _
--               → d y
-- & ret = ret
