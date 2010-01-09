module Examples.Nat where

open import Coinduction
open import Relation.Binary.PropositionalEquality1

open import Refl
open import Total
open import Desc
open import Pair.Unordered


data NatCon : Set where
  zero : NatCon
  suc  : NatCon

total-NatCon : Total NatCon
total-NatCon = record
           { compare = compare
           ; valid   = valid
           } where
  compare : (x y : NatCon) → Compare x y
  compare zero zero = eq _
  compare zero suc  = lt _ _
  compare suc  zero = gt _ _
  compare suc  suc  = eq _
  
  valid : (x y : NatCon) → compare x y ≡ uncompare (compare y x)
  valid zero zero = refl
  valid zero suc  = refl
  valid suc  zero = refl
  valid suc  suc  = refl

NatDesc : DelayDesc
NatDesc = arg NatCon total-NatCon case-con where
  case-con : NatCon → ∞₁ DelayDesc
  case-con zero = ♯₁ ret
  case-con suc  = ♯₁ NatDesc

ℕ = ⟦ NatDesc ⟧

two : ℕ
two = (arg suc
        (arg suc
          (arg zero ret)))

three : ℕ
three = (arg suc
          (arg suc
            (arg suc
              (arg zero ret))))

five : ℕ
five = (arg suc
         (arg suc
           (arg suc
             (arg suc
               (arg suc
                 (arg zero ret))))))

&ℕ = ⟦ & NatDesc ⟧

two,three : &ℕ
two,three = (arg eq (arg suc
              (arg eq (arg suc
                (arg lt (arg zero (arg suc (arg refl
                  (arg zero ret)))))))))

add : &ℕ → ℕ
add (arg eq (arg zero ret))                     = arg zero ret
add (arg eq (arg suc xy))                       = arg suc (arg suc (add xy))
add (arg lt (arg zero (arg suc  (arg refl y)))) = arg suc y
add (arg lt (arg zero (arg zero (arg () y))))
add (arg lt (arg suc  (arg zero (arg () y))))
add (arg lt (arg suc  (arg suc  (arg () y))))

_+_ : ℕ → ℕ → ℕ
x + y = add (drop-order x y)

add-commutes : ∀ x y → x + y ≡₁ y + x
add-commutes = &commutes add

add-works : two + three ≡₁ five
add-works = refl
