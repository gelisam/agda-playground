module FlatCont.Modal where

open import Data.Product
open import Relation.Unary
open import Pi
open import FlatCont

□ : ∀ {S P E}
  → Pred E
  → Pred (FlatCont S P E)
□ {P = P} Q (s ▹ c) = Π P λ p
                    → Q (c p)

◇ : ∀ {S P E}
  → Pred E
  → Pred (FlatCont S P E)
◇ {P = P} Q (s ▹ c) = Σ P λ p
                    → Q (c p)
