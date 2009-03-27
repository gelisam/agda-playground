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

lookup-ctx : ∀ {n}
           → Ctx n
           → Fin n
           → Type
lookup-ctx (ε    ) ()
lookup-ctx (Γ ▸ τ) zero    = τ
lookup-ctx (Γ ▸ τ) (suc i) = lookup-ctx Γ i
