module LamFin where

open import Data.Nat
open import Data.Fin
open import Data.Vec


-- a function over exactly n arguments of type α, returning β

infix 0 _-_→F_
_-_→F_ : Set → ℕ → Set
       → Set
α - zero  →F β = β
α - suc n →F β = α → α - n →F β

λF : ∀ {n α β}
   → (Vec α n → β)
   → α - n →F β
λF {zero}  f = f []
λF {suc n} f = λ x → λF {n} (λ xs → f (x ∷ xs))
