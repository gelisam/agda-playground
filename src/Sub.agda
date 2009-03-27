module Sub where

open import Data.Nat hiding (_≤_)
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
           → Δ ≤ Ψ
           → Δ ⊦ Γ sub
           → Ψ ⊦ Γ sub
weaken-sub Δ≤Ψ ε       = ε
weaken-sub Δ≤Ψ (σ ▸ e) = weaken-sub Δ≤Ψ σ ▸ weaken Δ≤Ψ e
