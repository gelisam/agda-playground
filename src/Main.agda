module Main where


open import Data.Function
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
  Γ ≤ Δ = ⟦ Δ ⟧c → ⟦ Γ ⟧c
  
  _⊦◇_ : Context → Type → Set
  Δ ⊦◇ τ = ∃ λ Γ → Γ ≤ Δ × Γ ⊦ τ

-- _≤_ is reflexive and transitive, so it's at least a preorder.
-- 
-- if it was antisymmetric (which it is if we use logical equivalence for equality),
-- it would be a partial order.
-- 
-- it's also monotonic and transitive. it there a special name for it?

reflexive : ∀ {Γ}
          → Γ ≤ Γ
reflexive = id

transitive : ∀ {Γ Δ Ψ}
           → Γ ≤ Δ
           →     Δ ≤ Ψ
           → Γ   ≤   Ψ
transitive f g = f ∘ g

monotonic : ∀ {Γ Δ τ}
          → Γ     ≤ Δ
          → Γ ▸ τ ≤ Δ ▸ τ
monotonic f x = f (proj₁ x) , proj₂ x

weaken : ∀ {Γ τ}
       → Γ ≤ Γ ▸ τ
weaken = proj₁
