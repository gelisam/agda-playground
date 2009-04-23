module FinCont.Modal where

open import Data.Product
open import Data.Fin
open import Relation.Unary
open import Pi
open import FinCont

□ : ∀ {S P E}
  → Pred E
  → Pred (FinCont S P E)
□ {P = P} Q (s ▹ c) = Π (Fin (P s)) λ p
                    → Q (c p)

◇ : ∀ {S P E}
  → Pred E
  → Pred (FinCont S P E)
◇ {P = P} Q (s ▹ c) = Σ (Fin (P s)) λ p
                    → Q (c p)
