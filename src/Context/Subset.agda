module Context.Subset where

open import Data.Nat hiding (_≤_)
open import Data.Fin hiding (_≤_)
open import Context
open import Context.Syntax


infix 1 _≤_
data _≤_ : {n m : ℕ} → Ctx n → Ctx m → Set where
  start : ε ≤ ε
  _keep : ∀ {n m τ}{Γ : Ctx n}{Δ : Ctx m}
        → Γ     ≤ Δ
        → Γ ▸ τ ≤ Δ ▸ τ
  _drop : ∀ {n m τ}{Γ : Ctx n}{Δ : Ctx m}
        → Γ ≤ Δ
        → Γ ≤ Δ ▸ τ

open import Data.Product
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

reindex : ∀ {n m}{Γ : Ctx n}{Δ : Ctx m}
        → (i : Fin n)
        → Γ ≤ Δ
        → Σ (Fin m) λ j
          → Γ !! i ≡ Δ !! j
reindex () start
reindex {suc n} {suc m} {Γ ▸ τ} {Δ ▸ .τ} zero (Γ≤Δ keep) = j , prf where
  j : Fin (suc m)
  j = zero
  
  prf : Γ ▸ τ !! zero ≡ Δ ▸ τ !! j
  prf = refl
reindex {suc n} {suc m} {Γ ▸ τ} {Δ ▸ .τ} (suc i) (Γ≤Δ keep) = j , prf where
  j,prf : Σ (Fin m) λ j
          → Γ !! i ≡ Δ !! j
  j,prf = reindex i Γ≤Δ
  
  j : Fin (suc m)
  j = suc (proj₁ j,prf)
  
  prf : Γ ▸ τ !! (suc i) ≡ Δ ▸ τ !! j
  prf =
    begin
      Γ ▸ τ !! (suc i)
    ≡⟨ byDef ⟩ 
      Γ !! i
    ≡⟨ proj₂ j,prf ⟩ 
      Δ !! (proj₁ j,prf)
    ≡⟨ byDef ⟩ 
      Δ ▸ τ !! j
    ∎
reindex {n} {suc m} {Γ} {Δ ▸ τ} i (Γ≤Δ drop) = j , prf where
  j,prf : Σ (Fin m) λ j
          → Γ !! i ≡ Δ !! j
  j,prf = reindex i Γ≤Δ
  
  j : Fin (suc m)
  j = suc (proj₁ j,prf)
  
  prf : Γ !! i ≡ Δ ▸ τ !! j
  prf =
    begin
      Γ !! i
    ≡⟨ proj₂ j,prf ⟩ 
      Δ !! (proj₁ j,prf)
    ≡⟨ byDef ⟩ 
      Δ ▸ τ !! j
    ∎
