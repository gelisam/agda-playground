module DepCont.Modal where

open import Data.Product
open import Relation.Unary
open import Pi
open import DepCont

□ : ∀ {S P E}
  → (∀ {p} → Pred (E p))
  → Pred (DepCont S P E)
□ {P = P} Q (s ▹ c) = Π P λ p
                    → Q (c p)

◇ : ∀ {S P E}
  → (∀ {p} → Pred (E p))
  → Pred (DepCont S P E)
◇ {P = P} Q (s ▹ c) = Σ P λ p
                    → Q (c p)
