module Cont.Modal where

open import Data.Product
open import Relation.Unary
open import Pi
open import Cont

□ : ∀ {S P E}
  → Pred E
  → Pred (Cont S P E)
□ {P = P} Q (s ▹ c) = Π (P s) λ p
                    → Q (c p)

◇ : ∀ {S P E}
  → Pred E
  → Pred (Cont S P E)
◇ {P = P} Q (s ▹ c) = Σ (P s) λ p
                    → Q (c p)
