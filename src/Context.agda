module Context where

open import Data.Nat
open import Data.Fin hiding (_+_)


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


open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

n≡n+0 : ∀ n
      → n ≡ n + zero
n≡n+0 zero =
  begin
    zero
  ≡⟨ byDef ⟩
    zero + zero
  ∎
n≡n+0 (suc n) =
  begin
    suc n
  ≡⟨ cong suc (n≡n+0 n) ⟩
    suc (n + zero)
  ≡⟨ byDef ⟩
    suc n + zero
  ∎

sn+m≡n+sm : ∀ n m
          → suc (n + m) ≡ n + suc m
sn+m≡n+sm zero m =
  begin
    suc (zero + m)
  ≡⟨ byDef ⟩
    suc m
  ≡⟨ byDef ⟩
    zero + suc m
  ∎
sn+m≡n+sm (suc n) m =
  begin
    suc (suc n + m)
  ≡⟨ byDef ⟩
    suc (suc (n + m))
  ≡⟨ cong suc (sn+m≡n+sm n m) ⟩
    suc (n + suc m)
  ≡⟨ byDef ⟩
    suc n + suc m
  ∎

infix 1 _++_
_++_ : ∀ {n m}
     → Ctx n
     → Ctx m
     → Ctx (n + m)
_++_ {n} {zero}  Γ ε       = subst Ctx (n≡n+0 n)       Γ
_++_ {n} {suc m} Γ (Δ ▸ τ) = subst Ctx (sn+m≡n+sm n m) ((Γ ++ Δ) ▸ τ)
