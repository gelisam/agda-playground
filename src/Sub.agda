module Sub where

open import Data.Nat hiding (_≤_)
open import Data.Fin hiding (_≤_)
open import Context
open import Term


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
