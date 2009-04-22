module List (α : Set) where
open import Data.Empty
open import Data.Unit
open import Data.Function
open import Data.Sum
open import W

List : Set
List = W (⊤ ⊎ α) ⟦_⟧ where
  ⟦_⟧ : ⊤ ⊎ α → Set
  ⟦ inj₁ tt ⟧ = ⊥
  ⟦ inj₂ α  ⟧ = ⊤

ε : List
ε = sup (inj₁ tt) λ()

infixr 5 _∷_
_∷_ : α → List → List
_∷_ x xs = sup (inj₂ x) (const xs)
