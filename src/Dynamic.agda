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

infix 0 _⇓_
data _⇓_ : {τ : Type}
         → ε ⊦ τ term
         →   ⊦ τ value
         → Set
           where
  unit : unit ⇓ value unit
  ƛ    : ∀ {τ₁ τ₂}
       → {e : ε ▸ τ₁ ⊦ τ₂ term}
       → ƛ e ⇓ value (ƛ e)
  eval : ∀ {τ₁ τ₂}
       → {e₁  : ε ⊦ τ₁ ⇾ τ₂ term}
       → {e₁' : ε ▸ τ₁ ⊦ τ₂ term}
       → {e₂  : ε ⊦ τ₁      term}
       → {v₂  :   ⊦ τ₁      value}
       → {e₃  : ε ⊦      τ₂ term}
       → {v₃  :   ⊦      τ₂ value}
       → e₁      ⇓ value (ƛ e₁')
       → e₂      ⇓ v₂
       → e₁' [ value➝term v₂ ] ⇓ v₃
       → e₁ ⋅ e₂ ⇓ v₃
