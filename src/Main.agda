module Main where

open import Data.Nat hiding (_≤_)
open import Data.Fin hiding (_≤_)
open import Context


infix 0 _⊦_term 
infixl 1 _⋅_
data _⊦_term {n : ℕ}(Γ : Ctx n) : Type → Set where
  var  : (i : Fin n)
       → Γ ⊦ Γ !! i  term
  unit : Γ ⊦ unit    term
  _⋅_  : ∀ {τ₁ τ₂}
       → Γ ⊦ τ₁ ⇾ τ₂ term
       → Γ ⊦ τ₁      term
       → Γ ⊦      τ₂ term
  ƛ    : ∀ {τ₁ τ₂}
       → Γ ▸ τ₁ ⊦ τ₂ term
       → Γ ⊦ τ₁ ⇾ τ₂ term

data Value : {τ : Type} → ε ⊦ τ term → Set where
  unit : Value unit
  ƛ    : ∀ {τ₁ τ₂}
       → (e : ε ▸ τ₁ ⊦ τ₂ term)
       → Value (ƛ e)

-- weaken : ∀ {n m τ}{Γ : Ctx n}{Δ : Ctx m}
--        → Γ ≤ Δ
--        → Γ ⊦ τ term
--        → Δ ⊦ τ term
-- weaken Γ≤Δ (var i) = var (reindex Γ≤Δ i)
-- weaken Γ≤Δ e = _
