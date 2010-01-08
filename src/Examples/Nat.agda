module Examples.Nat where

open import Coinduction

open import Refl
open import Total
open import Desc


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
two = arg suc
        (arg suc
          (arg zero ret))

three : ℕ
three = arg suc
          (arg suc
            (arg suc
              (arg zero ret)))
