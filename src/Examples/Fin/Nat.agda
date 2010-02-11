-- a version of Examples.Nat which uses (Fin 2) instead of NatCon
-- there is thus less boilerplate, at the cost of readability

module Examples.Fin.Nat where

open import Data.Nat hiding (ℕ; zero; suc; _+_)
open import Data.Fin hiding (_+_)
open import Coinduction
open import Relation.Binary.PropositionalEquality1

open import Refl
open import Total
open import Desc
open import Pair.Unordered
open import Examples.Fin


NatDesc : DelayDesc
NatDesc = arg (Fin 2) total-Fin case-con where
  case-con : Fin 2 → ∞₁ DelayDesc
  case-con zero       = ♯₁ ret
  case-con (suc zero) = ♯₁ NatDesc
  case-con (suc (suc ()))

ℕ = ⟦ NatDesc ⟧

z : ℕ
z = arg (# 0) ret

s : ℕ → ℕ
s x = arg (# 1) x

two : ℕ
two = s (s z)

three : ℕ
three = s (s (s z))

five : ℕ
five = s (s (s (s (s z))))

&ℕ = ⟦ & NatDesc ⟧

two,three : &ℕ
two,three = drop-order two three

add : &ℕ → ℕ
add (arg eq (arg zero           ret)) = z
add (arg eq (arg (suc zero)     xy )) = s (s (add xy))
add (arg eq (arg (suc (suc ())) _  ))
add (arg lt (arg zero           (arg (suc zero)     (arg refl y)))) = s y
add (arg lt (arg zero           (arg zero           (arg ()   y))))
add (arg lt (arg zero           (arg (suc (suc ())) _           )))
add (arg lt (arg (suc zero)     (arg zero           (arg ()   y))))
add (arg lt (arg (suc zero)     (arg (suc zero)     (arg ()   y))))
add (arg lt (arg (suc zero)     (arg (suc (suc ())) _           )))
add (arg lt (arg (suc (suc ())) _                                ))

_+_ : ℕ → ℕ → ℕ
x + y = add (drop-order x y)

add-commutes : ∀ x y → x + y ≡₁ y + x
add-commutes = &commutes add

add-works : two + three ≡₁ five
add-works = refl
