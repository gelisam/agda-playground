module Main where

open import Data.Unit
open import Data.Product

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


data PlainDesc : Set₁ where
  arg : ∀ A → Total A → (A → PlainDesc) → PlainDesc
  rec : PlainDesc →                       PlainDesc
  ret :                                   PlainDesc

⟦_⟧ : PlainDesc → Set → Set
⟦ arg A tA d ⟧ R = ∃ λ a → ⟦ d a ⟧ R
⟦ rec      d ⟧ R = R × ⟦ d ⟧ R
⟦ ret        ⟧ R = ⊤

data PlainData (d : PlainDesc) : Set where
  ⟨_⟩ : ⟦ d ⟧ (PlainData d) → PlainData d


lexicographic : ∀ {A B}
              → Total A
              → ((a : A) → Total (B a))
              → Total (Σ A B)
lexicographic {A} {B} tA tB = record
                            { compare = compare
                            ; valid   = valid
                            } where
  compare : (xx yy : Σ A B) → Compare xx yy
  compare (x , u) (y , v) with Total.compare tA x y
  ... | lt .x .y = lt (x , u) (y , v)
  ... | gt .x .y = gt _ _
  compare (.a , x) (.a , y) | eq a with Total.compare (tB a) x y
  ...   | lt .x .y = lt _ _
  ...   | gt .x .y = gt _ _
  compare (.a , .b) (.a , .b) | eq a | eq b = eq _
  
  valid : (xx yy : Σ A B)
        → compare xx yy ≡ uncompare (compare yy xx)
  valid (x , _) (y , _) with Total.compare tA x y
                           | Total.compare tA y x
                           | Total.valid tA x y
  ... | lt .x .y | gt .y .x | refl = refl
  ... | gt .x .y | lt .y .x | refl = refl
  ... | lt .x .y | lt .y .x | ()
  ... | gt .x .y | gt .y .x | ()
  valid (.a , _) (.a , _) | lt .a .a | eq a | ()
  valid (.a , _) (.a , _) | gt .a .a | eq a | ()
  valid (.a , _) (.a , _) | eq a | lt .a .a | ()
  valid (.a , _) (.a , _) | eq a | gt .a .a | ()
  valid (.a , x) (.a , y) | eq .a | eq a | refl with Total.compare (tB a) x y
                                                   | Total.compare (tB a) y x
                                                   | Total.valid (tB a) x y
  ...   | lt .x .y | gt .y .x | refl = refl
  ...   | gt .x .y | lt .y .x | refl = refl
  ...   | lt .x .y | lt .y .x | ()
  ...   | gt .x .y | gt .y .x | ()
  valid (.a , .b) (.a , .b) | eq .a | eq a | refl | lt .b .b | eq b | ()
  valid (.a , .b) (.a , .b) | eq .a | eq a | refl | gt .b .b | eq b | ()
  valid (.a , .b) (.a , .b) | eq .a | eq a | refl | eq b | lt .b .b | ()
  valid (.a , .b) (.a , .b) | eq .a | eq a | refl | eq b | gt .b .b | ()
  valid (.a , .b) (.a , .b) | eq .a | eq a | refl | eq .b | eq b | refl = refl
