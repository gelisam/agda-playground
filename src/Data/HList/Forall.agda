module Data.HList.Forall where
open import Data.List1
open import Data.HList
-- heterogenous ∀
-- foo : l∀ (α ∷ β ∷ []) λ αs → γ
-- foo : α → β → γ
-- foo = lλ λ hlist → ...

l∀ : ∀ αs → (HList αs → Set) → Set
l∀ []       f = f []
l∀ (α ∷ αs) f = (x : α) → l∀ αs λ xs → f (x ∷ xs)

_l→_ : List₁ Set → Set → Set
_l→_ αs β = l∀ αs λ _ → β

lλ : ∀ {αs f}
   → ((xs : HList αs) → f xs)
   → l∀ αs f
lλ {[]}     f = f []
lλ {α ∷ αs} f = λ x → lλ λ xs → f (x ∷ xs)

λl : ∀ {αs f}
   → (l∀ αs f)
   → ((xs : HList αs) → f xs)
λl f []       = f
λl f (x ∷ xs) = λl (f x) xs
