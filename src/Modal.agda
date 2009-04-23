module Modal (Shape : Set) (Pos : Shape → Set) where

open import Data.Product
import Cont
open Cont Shape Pos

private
  Π : (a : Set)
    → (a → Set)
    → Set
  Π a f = (x : a)
        → f x

□ : {α : Set}
  → Cont α
  → (α → Set)
  → Set
□ (shape ▹ el) P = Π (Pos shape) λ p
                 → P (el p)

◇ : {α : Set}
  → Cont α
  → (α → Set)
  → Set
◇ (shape ▹ el) P = Σ (Pos shape) λ p
                 → P (el p)
