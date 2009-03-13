module Main where


open import Data.Unit using (⊤)
open import Data.Product


infixr 5 _→t_
data Type : Set where
  unit : Type
  _→t_  : (τ₁ τ₂ : Type) → Type 

⟦_⟧t : Type → Set
⟦ unit ⟧t = ⊤
⟦ τ₁ →t τ₂ ⟧t = ⟦ τ₁ ⟧t → ⟦ τ₂ ⟧t


infixl 4 _▸_
data Context : Set where
  ε   : Context
  _▸_ : Context → Type → Context

⟦_⟧c : Context → Set
⟦ ε ⟧c = ⊤
⟦ Γ ▸ τ ⟧c = ⟦ Γ ⟧c × ⟦ τ ⟧t


mutual
  infix 3 _⊦_
  infix 3 _⊦◇_
  data _⊦_ : Context → Type → Set where
    var : ∀ {Γ τ}
        → Γ ▸ τ ⊦ τ
    _⋅_ : ∀ {Γ τ₁ τ₂}
        → Γ ⊦◇ τ₁ →t τ₂
        → Γ ⊦◇ τ₁
        → Γ ⊦ τ₂
    ƛ_  : ∀ {Γ τ₁ τ₂}
        → Γ ▸ τ₁ ⊦◇ τ₂
        → Γ ⊦ τ₁ →t τ₂
  
  infix 3 _≤_
  _≤_ : Context → Context → Set
  Γ ≤ Δ = ⟦ Γ ⟧c → ⟦ Δ ⟧c
  
  _⊦◇_ : Context → Type → Set
  Δ ⊦◇ τ = ∃ λ Γ → Γ ≤ Δ × Γ ⊦ τ
