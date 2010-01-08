module Main where

open import Examples.Nat


open import Coinduction

open import Refl
open import Total
open import Desc


_,_ : DelayDesc → DelayDesc → DelayDesc
ret        , b = b
arg A tA d , b = arg A tA d′ where
  d′ : A → ∞₁ DelayDesc
  d′ a = ♯₁ ♭₁ (d a) , b


data &Tag : Set where
  eq : &Tag
  lt : &Tag

total-&Tag : Total &Tag
total-&Tag = record
           { compare = compare
           ; valid   = valid
           } where
  compare : (x y : &Tag) → Compare x y
  compare eq eq = eq _
  compare eq lt = lt _ _
  compare lt eq = gt _ _
  compare lt lt = eq _
  
  valid : (x y : &Tag) → compare x y ≡ uncompare (compare y x)
  valid eq eq = refl
  valid eq lt = refl
  valid lt eq = refl
  valid lt lt = refl

&_ : DelayDesc → DelayDesc
& ret = ret
& arg A tA d = arg &Tag total-&Tag case-tag where
  case-tag : &Tag → ∞₁ DelayDesc
  case-tag eq = ♯₁ arg A tA λ a
              → ♯₁ & ♭₁ (d a)
  case-tag lt = ♯₁ arg A tA λ x
              → ♯₁ arg A tA λ y
              → ♯₁ arg (Total.compare tA x y ≡ lt x y) total-≡ λ _
              → ♯₁ ♭₁ (d x) , ♭₁ (d y)
