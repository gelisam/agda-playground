module Weak.Nat where
open import Data.Nat
open import Data.Fin hiding (_+_)

import Weak

⟦_⟧ : Fin 2 → ℕ
⟦ zero     ⟧ = 0
⟦ suc zero ⟧ = 1
⟦ suc (suc ()) ⟧

open Weak (Fin 2) ⟦_⟧


Nat : Set
Nat = Weak

z : Nat
z = sup (# 0) (childs 0)

s : Nat → Nat
s x = sup (# 1) (childs 1 x)
