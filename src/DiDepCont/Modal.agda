module DiDepCont.Modal where

open import Data.Product
open import Relation.Unary
open import Pi
open import DiDepCont

□ : ∀ {S P E}
  → (∀ {s p} → Pred (E s p))
  → Pred (DiDepCont S P E)
□ {P = P} Q (s ▹ c) = Π (P s) λ p
                    → Q (c p)

◇ : ∀ {S P E}
  → (∀ {s p} → Pred (E s p))
  → Pred (DiDepCont S P E)
◇ {P = P} Q (s ▹ c) = Σ (P s) λ p
                    → Q (c p)
