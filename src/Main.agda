module Main where

open import Data.Nat hiding (_≤_)
open import Data.Fin hiding (_≤_)
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Context



infix 4 _⊦_term 
infixl 5 _⋅_
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

weaken : ∀ {n m τ}{Γ : Ctx n}{Δ : Ctx m}
       → Γ ≤ Δ
       → Γ ⊦ τ term
       → Δ ⊦ τ term
weaken {n} {m} .{Γ !! i} {Γ} {Δ} Γ≤Δ (var i) = var_j where
  j,prf : Σ (Fin m) λ j
          → Γ !! i ≡ Δ !! j
  j,prf = reindex Γ≤Δ i
  
  j : Fin m
  j = proj₁ j,prf
  
  convert : Γ !! i ≡ Δ !! j
          → Δ ⊦ Δ !! j term
          → Δ ⊦ Γ !! i term
  convert prf e with Δ !! j
  convert refl e | .(Γ !! i) = e
  
  var_j = convert (proj₂ j,prf) (var j)
weaken Γ≤Δ unit = unit
weaken Γ≤Δ (e₁ ⋅ e₂) = (weaken Γ≤Δ e₁) ⋅ (weaken Γ≤Δ e₂)
weaken Γ≤Δ (ƛ e) = ƛ (weaken (Γ≤Δ keep) e)
