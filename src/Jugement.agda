open import Context
open import Relation.Binary
open import Data.Product

module Jugement (leq : Rel Context) where


mutual
  infix 3 _⊦_term
  infix 3 _⊦◇_term
  infixl 4 _⋅_
  data _⊦_term : Context → Type → Set where
    tt  : ε ⊦ unit term
    var : ∀ {Γ τ}
        → Γ ▸ τ ⊦ τ term
    _⋅_ : ∀ {Γ τ₁ τ₂}
        → Γ ⊦◇ τ₁ →t τ₂ term
        → Γ ⊦◇ τ₁       term
        → Γ ⊦        τ₂ term
    ƛ   : ∀ {Γ τ₁ τ₂}
        → Γ ▸ τ₁ ⊦◇ τ₂ term
        → Γ ⊦ τ₁ →t τ₂ term
  
  infix 3 _/_⊦_
  data _⊦◇_term (Δ : Context)(τ : Type) : Set where
    _/_⊦_ : (Γ : Context)
          → leq Γ Δ
          → Γ ⊦  τ term
          → Δ ⊦◇ τ term
