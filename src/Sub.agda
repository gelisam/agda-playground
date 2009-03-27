module Sub where

open import Data.Nat hiding (_≤_)
open import Data.Fin hiding (_≤_)
open import Context
open import Context.Properties
open import Term


private
  infix 5 _!!_
  _!!_ : ∀ {n}
       → Ctx n
       → Fin n
       → Type
  _!!_ = lookup-ctx

infix 0 _⊦_sub
data _⊦_sub {n : ℕ} (Δ : Ctx n) : {m : ℕ} → Ctx m → Set where
  ε   : Δ ⊦ ε sub
  _▸_ : {m : ℕ}{Γ : Ctx m}{τ : Type}
      → Δ ⊦  Γ     sub
      → Δ ⊦      τ term
      → Δ ⊦  Γ ▸ τ sub

weaken-sub : ∀ {n m l}{Δ : Ctx n}{Ψ : Ctx m}{Γ : Ctx l}
           → Δ ⊦ Γ sub
           → Δ ≤ Ψ
           → Ψ ⊦ Γ sub
weaken-sub ε       Δ≤Ψ = ε
weaken-sub (σ ▸ e) Δ≤Ψ = weaken-sub σ Δ≤Ψ ▸ weaken e Δ≤Ψ

lookup-sub : ∀ {n m}{Δ : Ctx n}{Γ : Ctx m}
           → Δ ⊦ Γ sub
           → (i : Fin m)
           → Δ ⊦ Γ !! i term
lookup-sub ε ()
lookup-sub (σ ▸ e) zero = e
lookup-sub (σ ▸ e) (suc i) = lookup-sub σ i

subst-term : ∀ {n m τ}{Δ : Ctx n}{Γ : Ctx m}
           → Γ ⊦ τ term
           → Δ ⊦ Γ sub
           → Δ ⊦ τ term
subst-term (var i)   σ = lookup-sub σ i
subst-term unit      σ = unit
subst-term (e₁ ⋅ e₂) σ = (subst-term e₁ σ) ⋅
                         (subst-term e₂ σ)
subst-term {n} {m} {τ₁ ⇾ τ₂} {Δ} {Γ} (ƛ e) σ = ƛ e' where
  ▸σ : Δ ▸ τ₁ ⊦ Γ sub
  ▸σ = weaken-sub σ (reflective drop)
  
  ▸σ▸ : Δ ▸ τ₁ ⊦ Γ ▸ τ₁ sub
  ▸σ▸ = ▸σ ▸ var zero
  
  e' : Δ ▸ τ₁ ⊦ τ₂ term
  e' = subst-term e ▸σ▸
