open import Context
open import Relation.Binary
open import Data.Product

module Jugement (leq : Rel Context) where


mutual
  infix 3 _⊦_
  infix 3 _⊦◇_
  infixl 4 _⋅_
  data _⊦_ : Context → Type → Set where
    tt  : ε ⊦ unit
    var : ∀ {Γ τ}
        → Γ ▸ τ ⊦ τ
    _⋅_ : ∀ {Γ τ₁ τ₂}
        → Γ ⊦◇ τ₁ →t τ₂
        → Γ ⊦◇ τ₁
        → Γ ⊦ τ₂
    ƛ   : ∀ {Γ τ₁ τ₂}
        → Γ ▸ τ₁ ⊦◇ τ₂
        → Γ ⊦ τ₁ →t τ₂
  
  _⊦◇_ : Context → Type → Set
  Δ ⊦◇ τ = ∃ λ Γ → leq Γ Δ × Γ ⊦ τ
