module Data.HList.Forall where
open import Data.List1
open import Data.HList
-- heterogenous ∀
-- foo : ∀h (α ∷ β ∷ []) λ αs → γ
-- foo : α → β → γ
-- foo = hλ λ hlist → ...

h∀ : ∀ αs → (HList αs → Set) → Set
h∀ []       f = f []
h∀ (α ∷ αs) f = (x : α) → h∀ αs λ xs → f (x ∷ xs)

hλ : ∀ αs {f}
   → ((xs : HList αs) → f xs)
   → h∀ αs f
hλ []       f = f []
hλ (α ∷ αs) f = λ x → hλ αs λ xs → f (x ∷ xs)
