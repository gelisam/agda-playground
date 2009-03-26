module Context where

open import Data.Nat hiding (_≤_)
open import Data.Fin hiding (_≤_)


infixr 7 _⇾_
data Type : Set where
  unit : Type
  _⇾_  : Type → Type → Type

infixl 6 _▸_
data Ctx : ℕ → Set where
  ε   : Ctx zero
  _▸_ : ∀ {n}
      → Ctx n → Type → Ctx (suc n)

infix 5 _!!_
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

open import Data.Product
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

reindex : ∀ {n m}{Γ : Ctx n}{Δ : Ctx m}
        → Γ ≤ Δ
        → (i : Fin n)
        → Σ (Fin m) λ j
          → Γ !! i ≡ Δ !! j
reindex start ()
reindex {suc n} {suc m} {Γ ▸ τ} {Δ ▸ .τ} (Γ≤Δ keep) zero = j , prf where
  j : Fin (suc m)
  j = zero
  
  prf : Γ ▸ τ !! zero ≡ Δ ▸ τ !! j
  prf = refl
reindex {suc n} {suc m} {Γ ▸ τ} {Δ ▸ .τ} (Γ≤Δ keep) (suc i) = j , prf where
  j,prf : Σ (Fin m) λ j
          → Γ !! i ≡ Δ !! j
  j,prf = reindex Γ≤Δ i
  
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
reindex {n} {suc m} {Γ} {Δ ▸ τ} (Γ≤Δ drop) i = j , prf where
  j,prf : Σ (Fin m) λ j
          → Γ !! i ≡ Δ !! j
  j,prf = reindex Γ≤Δ i
  
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
