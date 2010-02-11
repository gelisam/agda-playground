module Examples.Fin where

open import Data.Nat hiding (compare)
open import Data.Fin

open import Refl
open import Total


total-Fin : ∀ {n} → Total (Fin n)
total-Fin = record
          { compare = compare
          ; valid   = valid
          } where
  compare : ∀ {n} → (x y : Fin n) → Compare x y
  compare {zero}  ()      ()
  compare {suc n} zero     zero     = eq _
  compare {suc n} zero     (suc  y) = lt _ _
  compare {suc n} (suc  x) zero     = gt _ _
  compare {suc n} (suc  x) (suc  y) with compare x y
  compare {suc n} (suc .x) (suc .y) | lt x y = lt _ _
  compare {suc n} (suc .x) (suc .x) | eq  x  = eq  _
  compare {suc n} (suc .x) (suc .y) | gt x y = gt _ _
  
  valid : ∀ {n} → (x y : Fin n) → compare x y ≡ uncompare (compare y x)
  valid {zero}  ()      ()
  valid {suc n} zero     zero     = refl
  valid {suc n} zero     (suc  y) = refl
  valid {suc n} (suc  x) zero     = refl
  valid {suc n} (suc  x) (suc  y) with compare x y | compare y x | valid x y
  valid {suc n} (suc .x) (suc .y) | lt  x  y | lt .y .x | ()
  valid {suc n} (suc .x) (suc .y) | gt  x  y | gt .y .x | ()
  valid {suc n} (suc .x) (suc .x) | eq x     | lt .x .x | ()
  valid {suc n} (suc .x) (suc .x) | eq x     | gt .x .x | ()
  valid {suc n} (suc .x) (suc .x) | lt .x .x | eq x     | ()
  valid {suc n} (suc .x) (suc .x) | gt .x .x | eq x     | ()
  valid {suc n} (suc .x) (suc .y) | lt x y | gt .y .x | refl = refl
  valid {suc n} (suc .x) (suc .x) | eq  x  | eq  .x   | refl = refl
  valid {suc n} (suc .x) (suc .y) | gt x y | lt .y .x | refl = refl
