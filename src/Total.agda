module Total where

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
