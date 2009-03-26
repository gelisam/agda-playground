module Main where

open import Data.Nat
open import Data.Fin


infixr 3 _⇾_
data Type : Set where
  Unit : Type
  _⇾_  : Type → Type → Type

infixl 2 _▸_
data Ctx : ℕ → Set where
  ε   : Ctx zero
  _▸_ : ∀ {n}
      → Ctx n → Type → Ctx (suc n)

infix 1 _!!_
_!!_ : ∀ {n} → Ctx n → Fin n → Type
ε     !! ()
Γ ▸ τ !! zero    = τ
Γ ▸ τ !! (suc n) = Γ !! n

infix 0 _⊦_term 
infixl 1 _⋅_
data _⊦_term {n : ℕ}(Γ : Ctx n) : Type → Set where
  var  : (i : Fin n)
       → Γ ⊦ Γ !! i  term
  unit : Γ ⊦ Unit    term
  _⋅_  : ∀ {τ₁ τ₂}
       → Γ ⊦ τ₁ ⇾ τ₂ term
       → Γ ⊦ τ₁      term
       → Γ ⊦      τ₂ term
  ƛ    : ∀ {τ₁ τ₂}
       → Γ ▸ τ₁ ⊦ τ₂ term
       → Γ ⊦ τ₁ ⇾ τ₂ term
