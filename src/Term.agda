module Term where

open import Data.Nat hiding (_≤_)
open import Data.Fin hiding (_≤_)
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Context
open import Context.Syntax
open import Context.Subset


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

weaken : ∀ {n m τ}{Γ : Ctx n}{Δ : Ctx m}
       → Γ ⊦ τ term
       → Γ ≤ Δ
       → Δ ⊦ τ term
weaken {n} {m} .{Γ !! i} {Γ} {Δ} (var i) Γ≤Δ = var_j where
  j,prf : Σ (Fin m) λ j
          → Γ !! i ≡ Δ !! j
  j,prf = reindex i Γ≤Δ
  
  j : Fin m
  j = proj₁ j,prf
  
  convert : Γ !! i ≡ Δ !! j
          → Δ ⊦ Δ !! j term
          → Δ ⊦ Γ !! i term
  convert prf e with Δ !! j
  convert refl e | .(Γ !! i) = e
  
  var_j = convert (proj₂ j,prf) (var j)
weaken unit      Γ≤Δ = unit
weaken (e₁ ⋅ e₂) Γ≤Δ = (weaken e₁ Γ≤Δ) ⋅
                       (weaken e₂ Γ≤Δ)
weaken (ƛ e)     Γ≤Δ = ƛ (weaken e (Γ≤Δ keep))
