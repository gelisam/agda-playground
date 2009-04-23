module FlatDepCont.Modal where

open import Data.Product
open import Relation.Unary
open import Pi
open import FlatDepCont

□ : ∀ {S P E}
  → (∀ {p} → Pred (E p))
  → Pred (FlatDepCont S P E)
□ {P = P} Q (s ▹ c) = Π P λ p
                    → Q (c p)

◇ : ∀ {S P E}
  → (∀ {p} → Pred (E p))
  → Pred (FlatDepCont S P E)
◇ {P = P} Q (s ▹ c) = Σ P λ p
                    → Q (c p)
