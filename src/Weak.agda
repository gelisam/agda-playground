open import Data.Nat


module Weak (Shape : Set) (⟦_⟧ : Shape → ℕ) where

open import Data.Fin
open import Data.Vec
open import LamFin


-- Weak W types, which always use Fin positions.
-- is it really weaker than full W types?

data Weak : Set where
  sup : (shape : Shape)
      → (Fin ⟦ shape ⟧ → Weak)
      → Weak

wrec : ∀ {R : Weak → Set}
     → (w : Weak)
     → (branches : (shape : Shape)
                 → (child : Fin ⟦ shape ⟧ → Weak)
                 → (rec   : (pos : Fin ⟦ shape ⟧)
                          → R (child pos))
                 → R (sup shape child))
     → R w
wrec {R} (sup shape child) branches = r where
  r = branches
        shape
        child
        λ pos → wrec {R} (child pos) branches

childs : ∀ n
       → Weak - n →F (Fin n → Weak)
childs n = λF lookup' where
  lookup' : Vec Weak n → Fin n → Weak
  lookup' xs i = lookup i xs
