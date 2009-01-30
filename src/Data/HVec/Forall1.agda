module Data.HVec.Forall where
open import Data.Vec1
open import Data.HVec
-- heterogenous ∀
-- foo : v∀₁ (α ∷ β ∷ []) λ αs → P γ
-- foo : α → β → P γ
-- foo = vλ₁ λ hvec → ...

v∀₁ : ∀ {n}(αs : Vec₁ Set n) → (HVec n αs → Set) → Set
v∀₁ []       f = f []
v∀₁ (α ∷ αs) f = (x : α) → v∀₁ αs λ xs → f (x ∷ xs)

vλ₁ : ∀ {n}(αs : Vec₁ Set n) {f}
    → ((xs : HVec n αs) → f xs)
    → v∀ αs f
vλ₁ []       f = f []
vλ₁ (α ∷ αs) f = λ x → vλ₁ αs λ xs → f (x ∷ xs)

_v→_ : ∀ {n} → Vec₁ Set n → Set → Set
_v→_ αs β = v∀₁ αs λ _ → β
