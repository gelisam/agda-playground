module Context.Properties where

open import Data.Nat hiding (_≤_)
open import Context


reflective : ∀ {n}{Γ : Ctx n}
           → Γ ≤ Γ
reflective {Γ = ε}     = start
reflective {Γ = Γ ▸ τ} = reflective keep
