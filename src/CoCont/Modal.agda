module CoCont.Modal where

open import Data.Product
open import Relation.Unary
open import Pi
open import CoCont

□ : ∀ {S P E}
  → (∀ {s} → Pred (E s))
  → Pred (CoCont S P E)
□ {P = P} Q (s ▹ c) = Π P λ p
                    → Q (c p)

◇ : ∀ {S P E}
  → (∀ {s} → Pred (E s))
  → Pred (CoCont S P E)
◇ {P = P} Q (s ▹ c) = Σ P λ p
                    → Q (c p)
