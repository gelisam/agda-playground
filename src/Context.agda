module Context where

open import Data.Nat hiding (_≤_)
open import Data.Fin hiding (_≤_)


infixr 3 _⇾_
data Type : Set where
  unit : Type
  _⇾_  : Type → Type → Type

infixl 2 _▸_
data Ctx : ℕ → Set where
  ε   : Ctx zero
  _▸_ : ∀ {n}
      → Ctx n → Type → Ctx (suc n)

infix 1 _!!_
_!!_ : ∀ {n}
     → Ctx n
     → Fin n
     → Type
ε     !! ()
Γ ▸ τ !! zero    = τ
Γ ▸ τ !! (suc n) = Γ !! n

infix 1 _≤_
data _≤_ : {n m : ℕ} → Ctx n → Ctx m → Set where
  start : ε ≤ ε
  _keep : ∀ {n m τ}{Γ : Ctx n}{Δ : Ctx m}
        → Γ     ≤ Δ
        → Γ ▸ τ ≤ Δ ▸ τ
  _drop : ∀ {n m τ}{Γ : Ctx n}{Δ : Ctx m}
        → Γ ≤ Δ
        → Γ ≤ Δ ▸ τ

reindex : ∀ {n m}{Γ : Ctx n}{Δ : Ctx m}
        → Γ ≤ Δ
        → Fin n
        → Fin m
reindex start ()
reindex (Γ≤Δ keep) zero    = zero
reindex (Γ≤Δ keep) (suc i) = suc (reindex Γ≤Δ i)
reindex (Γ≤Δ drop) i       = suc (reindex Γ≤Δ i)
