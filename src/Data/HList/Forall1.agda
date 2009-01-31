module Data.HList.Forall1 where
open import Data.List1
open import Data.HList
-- heterogenous ∀
-- foo : l∀ (α ∷ β ∷ []) λ αs → P γ
-- foo : α → β → P γ
-- foo = lλ λ hlist → ...

l∀₁ : ∀ αs → (HList αs → Set1) → Set1
l∀₁ []       f = f []
l∀₁ (α ∷ αs) f = (x : α) → l∀₁ αs λ xs → f (x ∷ xs)

_l→₁_ : List₁ Set → Set1 → Set1
_l→₁_ αs β = l∀₁ αs λ _ → β

lλ₁ : ∀ {αs f}
    → ((xs : HList αs) → f xs)
    → l∀₁ αs f
lλ₁ {[]}     f = f []
lλ₁ {α ∷ αs} f = λ x → lλ₁ λ xs → f (x ∷ xs)

λl₁ : ∀ {αs f}
    → (l∀₁ αs f)
    → ((xs : HList αs) → f xs)
λl₁ f []       = f
λl₁ f (x ∷ xs) = λl₁ (f x) xs
