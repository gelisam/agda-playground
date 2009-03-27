module Sub.Syntax where

open import Context
open import Term
open import Sub


infix 2 _[_]
_[_] : ∀ {n τ₁ τ₂}{Γ : Ctx n}
     → Γ ▸ τ₁ ⊦ τ₂ term
     → Γ ⊦ τ₁      term
     → Γ ⊦      τ₂ term
e₁ [ e₂ ] = subst-term e₁ (id-sub ▸ e₂)
