module Syntactic where


open import Context

infix 3 _≤_
data _≤_ : Context → Context → Set where
  start : ε ≤ ε
  _keep : ∀ {Γ Δ τ}
        → Γ     ≤ Δ
        → Γ ▸ τ ≤ Δ ▸ τ
  _drop : ∀ {Γ Δ τ}
        → Γ ≤ Δ
        → Γ ≤ Δ ▸ τ


-- The syntactic _≤_ has the same basic properties as the semantic _≤_.

reflexive : ∀ {Γ}
          → Γ ≤ Γ
reflexive {ε}     = start
reflexive {Γ ▸ τ} = reflexive keep

transitive : ∀ {Γ Δ Ψ}
           → Γ ≤ Δ
           →     Δ ≤ Ψ
           → Γ   ≤   Ψ
transitive start      start      = start
transitive (Γ≤Δ keep) (Δ≤Ψ keep) = (transitive Γ≤Δ Δ≤Ψ) keep
transitive (Γ≤Δ drop) (Δ≤Ψ keep) = (transitive Γ≤Δ Δ≤Ψ) drop
transitive Γ≤Δ (Δ≤Ψ drop) = (transitive Γ≤Δ Δ≤Ψ) drop

monotonic : ∀ {Γ Δ τ}
          → Γ     ≤ Δ
          → Γ ▸ τ ≤ Δ ▸ τ
monotonic = _keep

weaken : ∀ {Γ τ}
       → Γ ≤ Γ ▸ τ
weaken = reflexive drop

initial : ∀ {Γ}
        → ε ≤ Γ
initial {ε}     = start
initial {Γ ▸ τ} = initial drop


open import Data.Product
import Jugement
open Jugement _≤_

import Substitution
open Substitution _≤_ reflexive transitive monotonic weaken

lookup-sub : ∀ {Γ τ Δ Ψ}
           → Ψ ⊦ Δ sub
           → Γ ▸ τ ≤ Δ
           → Ψ ⊦◇ τ term
lookup-sub ε ()
lookup-sub (σ ▸ e) (Γ≤Δ keep) = e
lookup-sub (σ ▸ e) (Γ▸τ≤Δ drop) = lookup-sub σ Γ▸τ≤Δ

partial-sub : ∀ {Δ Ψ Γ}
           → Ψ ⊦ Δ sub
           → Γ ≤ Δ
           → Ψ ⊦ Γ sub
partial-sub ε       start = ε
partial-sub (σ ▸ e) (Γ≤Δ keep) = partial-sub σ Γ≤Δ ▸ e
partial-sub (σ ▸ e) (Γ≤Δ drop) = partial-sub σ Γ≤Δ

subst : ∀ {Δ Ψ τ}
      → Δ ⊦◇ τ term
      → Ψ ⊦  Δ sub
      → Ψ ⊦◇ τ term
subst (ε     / ε≤Δ   ⊦ tt ) σ = ε / initial ⊦ tt
subst (Γ ▸ τ / Γ▸τ≤Δ ⊦ var) σ = lookup-sub σ Γ▸τ≤Δ
subst {Δ} {Ψ} (Γ / Γ≤Δ ⊦ e₁ ⋅ e₂) σ = Ψ / reflexive ⊦
  subst e₁ (partial-sub σ Γ≤Δ) ⋅
  subst e₂ (partial-sub σ Γ≤Δ)
subst {Δ} {Ψ} {τ₁ →t τ₂} (Γ / Γ≤Δ ⊦ ƛ eΓ▸τ₁) σ = eΨ where
  σΔ : Ψ ▸ τ₁ ⊦ Δ sub
  σΔ = weaken-sub σ weaken
  
  σΔ▸τ₁ : Ψ ▸ τ₁ ⊦ Δ ▸ τ₁ sub
  σΔ▸τ₁ = σΔ ▸ (Ψ ▸ τ₁ / reflexive ⊦ var)
  
  σΓ▸τ₁ : Ψ ▸ τ₁ ⊦ Γ ▸ τ₁ sub
  σΓ▸τ₁ = partial-sub σΔ▸τ₁ (Γ≤Δ keep)
  
  eΨ▸τ₁ : Ψ ▸ τ₁ ⊦◇ τ₂ term
  eΨ▸τ₁ = subst eΓ▸τ₁ σΓ▸τ₁
  
  eΨ : Ψ ⊦◇ τ₁ →t τ₂ term
  eΨ = Ψ / reflexive ⊦ ƛ eΨ▸τ₁
