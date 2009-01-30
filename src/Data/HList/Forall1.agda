module Data.HList.Forall1 where
open import Data.List1
open import Data.HList
-- heterogenous ∀
-- foo : ∀h (α ∷ β ∷ []) λ αs → γ
-- foo : α → β → γ
-- foo = hλ λ hlist → ...

h∀₁ : ∀ αs → (HList αs → Set1) → Set1
h∀₁ []       f = f []
h∀₁ (α ∷ αs) f = (x : α) → h∀₁ αs λ xs → f (x ∷ xs)

hλ₁ : ∀ αs {f}
    → ((xs : HList αs) → f xs)
    → h∀₁ αs f
hλ₁ []       f = f []
hλ₁ (α ∷ αs) f = λ x → hλ₁ αs λ xs → f (x ∷ xs)
