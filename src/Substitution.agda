open import Context

module Substitution
  (leq : Context → Context → Set)
  (reflexive : ∀ {Γ}
             → leq Γ Γ)
  (transitive : ∀ {Γ Δ Ψ}
              → leq Γ Δ
              → leq   Δ Ψ
              → leq Γ   Ψ)
  (monotonic : ∀ {Γ Δ τ}
             → leq  Γ       Δ
             → leq (Γ ▸ τ) (Δ ▸ τ))
  (weaken : ∀ {Γ τ}
          → leq Γ (Γ ▸ τ))
where

private
  infix 3 _≤_
  _≤_ = leq

import Jugement
open Jugement _≤_
open import Data.Product

weaken-◇ : ∀ {Δ Ψ τ}
         → Δ ⊦◇ τ term
         → Δ ≤ Ψ
         → Ψ ⊦◇ τ term
weaken-◇ {Δ} {Ψ} (Γ / Γ≤Δ ⊦ e) Δ≤Ψ = Γ / Γ≤Ψ ⊦ e where
  Γ≤Ψ : Γ ≤ Ψ
  Γ≤Ψ = transitive Γ≤Δ Δ≤Ψ


infix 0 _⊦_sub
data _⊦_sub (Δ : Context) : Context → Set where
  ε   : Δ ⊦ ε sub
  _▸_ : {Γ : Context}{τ : Type}
      → Δ ⊦  Γ     sub
      → Δ ⊦◇     τ term
      → Δ ⊦  Γ ▸ τ sub

weaken-sub : ∀ {Δ Ψ Γ}
           → Δ ⊦ Γ sub
           → Δ ≤ Ψ
           → Ψ ⊦ Γ sub
weaken-sub ε       Δ≤Ψ = ε
weaken-sub (σ ▸ e) Δ≤Ψ = weaken-sub σ Δ≤Ψ ▸ weaken-◇ e Δ≤Ψ
