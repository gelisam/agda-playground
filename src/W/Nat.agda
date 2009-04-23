module W.Nat where

open import Data.Empty
open import Data.Unit
open import Data.Function
open import W

data Tag : Set where
  Zero : Tag
  Succ : Tag

⟦_⟧ : Tag → Set
⟦ Zero ⟧ = ⊥
⟦ Succ ⟧ = ⊤

Nat : Set
Nat = W Tag ⟦_⟧

zero : Nat
zero = sup Zero λ()

succ : Nat → Nat
succ n = sup Succ (const n)

-- using natrec, what is add, mul, and exp?
natrec : Nat → Nat → (Nat → Nat → Nat) → Nat
natrec a b c = wrec {γ = λ _ → Nat} a f
  where
    f : (y : Tag) → (⟦ y ⟧ → Nat) → (⟦ y ⟧ → Nat) → Nat
    f Zero z u = b
    f Succ z u = c (z tt) (u tt)
