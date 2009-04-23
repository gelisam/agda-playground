module Weak.Vector (α : Set) where
open import Data.Unit
open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Product
open import Data.Function
open import Weak


Vector : ℕ → Set
Vector zero = Weak ⊤ (const 0)
Vector (suc n) = Weak (α × Vector n) (const 0)

ε : Vector zero
ε = sup tt (childs _ _ 0)

infixr 5 _∷_
_∷_ : ∀ {n} → α → Vector n → Vector (suc n)
_∷_ {n} x xs = sup (x , xs) (childs _ _ 0)
