module Syntactic where


open import Context

infix 3 _≤_
data _≤_ : Context → Context → Set where
  start : ε ≤ ε
  _keep : ∀ {Γ Δ τ}
        → Γ     ≤ Δ
        → Γ ▸ τ ≤ Δ ▸ τ
  _skip : ∀ {Γ Δ τ}
        → Γ ≤ Δ
        → Γ ≤ Δ ▸ τ

import Jugement
open Jugement _≤_


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
transitive (Γ≤Δ skip) (Δ≤Ψ keep) = (transitive Γ≤Δ Δ≤Ψ) skip
transitive Γ≤Δ (Δ≤Ψ skip) = (transitive Γ≤Δ Δ≤Ψ) skip

monotonic : ∀ {Γ Δ τ}
          → Γ     ≤ Δ
          → Γ ▸ τ ≤ Δ ▸ τ
monotonic = _keep

weaken : ∀ {Γ τ}
       → Γ ≤ Γ ▸ τ
weaken = reflexive skip

initial : ∀ {Γ}
        → ε ≤ Γ
initial {ε}     = start
initial {Γ ▸ τ} = initial skip
