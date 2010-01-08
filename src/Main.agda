module Main where

open import Examples.Nat


open import Coinduction
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality1

open import Total
open import Total1
open import Desc


total-⟦_⟧ : ∀ d → Total₁ ⟦ d ⟧
total-⟦ d ⟧ = record
            { compare = compare d
            ; valid   = valid d
            } where
  compare : ∀ d → (xx yy : ⟦ d ⟧) → Compare₁ xx yy
  compare ret ret ret = eq _
  compare (arg A tA d) (arg x _) (arg y _) with Total.compare tA x y
  ... | lt .x .y = lt _ _
  ... | gt .x .y = gt _ _
  compare (arg A tA d) (arg .a x) (arg .a y) | eq a with compare (♭₁ (d a)) x y
  ... | lt .x .y = lt _ _
  ... | gt .x .y = gt _ _
  compare (arg A tA d) (arg .a .b) (arg .a .b) | eq a | eq b = eq _
  
  valid : ∀ d xx yy
        → compare d xx yy ≡₁ uncompare₁ (compare d yy xx)
  valid ret ret ret = refl
  valid (arg A tA d) (arg x _) (arg y _) with Total.compare tA x y
                                            | Total.compare tA y x
                                            | Total.valid tA x y
  ... | lt .x .y | gt .y .x | refl = refl
  ... | gt .x .y | lt .y .x | refl = refl
  ... | lt .x .y | lt .y .x | ()
  ... | gt .x .y | gt .y .x | ()
  valid (arg A tA d) (arg .a _) (arg .a _) | lt .a .a | eq a | ()
  valid (arg A tA d) (arg .a _) (arg .a _) | gt .a .a | eq a | ()
  valid (arg A tA d) (arg .a _) (arg .a _) | eq a | lt .a .a | ()
  valid (arg A tA d) (arg .a _) (arg .a _) | eq a | gt .a .a | ()
  valid (arg A tA d) (arg .a x) (arg .a y) | eq .a | eq a | refl with compare (♭₁ (d a)) x y
                                                                    | compare (♭₁ (d a)) y x
                                                                    | valid   (♭₁ (d a)) x y
  ...   | lt .x .y | gt .y .x | refl = refl
  ...   | gt .x .y | lt .y .x | refl = refl
  ...   | lt .x .y | lt .y .x | ()
  ...   | gt .x .y | gt .y .x | ()
  valid (arg A tA d) (arg .a .b) (arg .a .b) | eq .a | eq a | refl | lt .b .b | eq b | ()
  valid (arg A tA d) (arg .a .b) (arg .a .b) | eq .a | eq a | refl | gt .b .b | eq b | ()
  valid (arg A tA d) (arg .a .b) (arg .a .b) | eq .a | eq a | refl | eq b | lt .b .b | ()
  valid (arg A tA d) (arg .a .b) (arg .a .b) | eq .a | eq a | refl | eq b | gt .b .b | ()
  valid (arg A tA d) (arg .a .b) (arg .a .b) | eq .a | eq a | refl | eq .b | eq b | refl = refl


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
