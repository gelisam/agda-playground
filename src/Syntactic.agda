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
