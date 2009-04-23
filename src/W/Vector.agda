module W.Vector (α : Set) where
open import Data.Product
open import Data.Nat
open import Data.Empty
open import Data.Unit
open import Data.Function
open import W

Vector : ℕ → Set
Vector zero = W ⊤ ⟦_⟧ where
  ⟦_⟧ : ⊤ → Set
  ⟦ tt ⟧ = ⊥
Vector (suc n) = W (α × Vector n) ⟦_⟧ where
  ⟦_⟧ : (α × Vector n) → Set
  ⟦ x , xs ⟧ = ⊥

ε : Vector zero
ε = sup tt λ()

infixr 5 _∷_
_∷_ : ∀ {n} → α → Vector n → Vector (suc n)
_∷_ x xs = sup (x , xs) λ()
