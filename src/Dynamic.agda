module Dynamic where

open import Sub
open import Sub.Syntax
open import Context
open import Term
open import Value


infix 0 _∼>_
data _∼>_ : {τ : Type}
          → ε ⊦ τ term
          → ε ⊦ τ term
          → Set
          where
  app₁ : ∀ {τ₁ τ₂}
       → {e₁ e₁' : ε ⊦ τ₁ ⇾ τ₂ term}
       → {e₂     : ε ⊦ τ₁      term}
       → e₁      ∼> e₁'
       → e₁ ⋅ e₂ ∼> e₁' ⋅ e₂
  app₂ : ∀ {τ₁ τ₂}
       → {e₁     : ε ⊦ τ₁ ⇾ τ₂ term}
       → {e₂ e₂' : ε ⊦ τ₁      term}
       → Value e₁
       →      e₂ ∼>      e₂'
       → e₁ ⋅ e₂ ∼> e₁ ⋅ e₂
  β    : ∀ {τ₁ τ₂}
       → {e₁ : ε ▸ τ₁ ⊦ τ₂ term}
       → {e₂ : ε ⊦ τ₁      term}
       → (ƛ e₁) ⋅ e₂ ∼> e₁ [ e₂ ]
