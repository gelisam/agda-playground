module DiCont.Modal where

open import Data.Product
open import Relation.Unary
open import Pi
open import DiCont

□ : ∀ {S P E}
  → (∀ {s} → Pred (E s))
  → Pred (DiCont S P E)
□ {P = P} Q (s ▹ c) = Π (P s) λ p
                    → Q (c p)

◇ : ∀ {S P E}
  → (∀ {s} → Pred (E s))
  → Pred (DiCont S P E)
◇ {P = P} Q (s ▹ c) = Σ (P s) λ p
                    → Q (c p)
