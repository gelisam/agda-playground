module Total where

open import Data.Empty
open import Relation.Binary.PropositionalEquality


data Compare {A : Set} : A → A → Set where
  lt : ∀ x y → Compare x y
  eq : ∀  x  → Compare x x
  gt : ∀ x y → Compare x y

uncompare : ∀ {A x y}
          → Compare {A} x y
          → Compare {A} y x
uncompare (lt x y) = gt y x
uncompare (eq  x ) = eq  x
uncompare (gt x y) = lt y x

record Total (A : Set) : Set where
  field
    compare : (x y : A) → Compare x y
    valid   : (x y : A)
            → compare x y ≡ uncompare (compare y x)
  
  gt-lt : ∀ {x y}
        → compare x y ≡ gt x y
        → compare y x ≡ lt y x
  gt-lt {x}  {y}  prf with compare x y | compare y x | valid x y
  gt-lt {x}  {y}  () | lt .x .y | _ | _
  gt-lt {.a} {.a} () | eq a     | _ | _
  gt-lt {x}  {y}  refl | gt .x .y | gt .y .x | ()
  gt-lt {.a} {.a} refl | gt .a .a | eq a     | ()
  gt-lt {x}  {y}  refl | gt .x .y | lt .y .x | refl = refl
  
  lt-lt : ∀ x y
        → compare x y ≡ lt x y
        → compare y x ≡ lt y x
        → ⊥
  lt-lt x y p q with compare x y | compare y x | valid x y
  lt-lt .a .a ()   q    | eq a     | _        | _
  lt-lt .a .a p    ()   | _        | eq a     | _
  lt-lt x  y  ()   q    | gt .x .y | _        | _
  lt-lt x  y  p    ()   | _        | gt .y .x | _
  lt-lt x  y  refl refl | lt .x .y | lt .y .x | ()
  
  gt-gt : ∀ x y
        → compare x y ≡ gt x y
        → compare y x ≡ gt y x
        → ⊥
  gt-gt x y p q with compare x y | compare y x | valid x y
  gt-gt .a .a ()   q    | eq a     | _        | _
  gt-gt .a .a p    ()   | _        | eq a     | _
  gt-gt x  y  ()   q    | lt .x .y | _        | _
  gt-gt x  y  p    ()   | _        | lt .y .x | _
  gt-gt x  y  refl refl | gt .x .y | gt .y .x | ()
  
  eq-lt : ∀ a
        → compare a a ≡ lt a a
        → ⊥
  eq-lt a p with compare a a | valid a a
  eq-lt a ()   | eq .a    | _
  eq-lt a ()   | gt .a .a | _
  eq-lt a refl | lt .a .a | ()
  
  eq-gt : ∀ a
        → compare a a ≡ gt a a
        → ⊥
  eq-gt a p with compare a a | valid a a
  eq-gt a ()   | eq .a    | _
  eq-gt a ()   | lt .a .a | _
  eq-gt a refl | gt .a .a | ()
