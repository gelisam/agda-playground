module Data.HVec.Forall where
open import Data.Vec1
open import Data.HVec
-- heterogenous ∀
-- foo : v∀ (α ∷ β ∷ []) λ αs → γ
-- foo : α → β → γ
-- foo = vλ λ hvec → ...

v∀ : ∀ {n}(αs : Vec₁ Set n) → (HVec n αs → Set) → Set
v∀ []       f = f []
v∀ (α ∷ αs) f = (x : α) → v∀ αs λ xs → f (x ∷ xs)

vλ : ∀ {n}(αs : Vec₁ Set n) {f}
   → ((xs : HVec n αs) → f xs)
   → v∀ αs f
vλ []       f = f []
vλ (α ∷ αs) f = λ x → vλ αs λ xs → f (x ∷ xs)

_v→_ : ∀ {n} → Vec₁ Set n → Set → Set
_v→_ αs β = v∀ αs λ _ → β
