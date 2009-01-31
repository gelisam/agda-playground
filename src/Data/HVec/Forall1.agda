module Data.HVec.Forall1 where
open import Data.Vec1
open import Data.HVec
-- heterogenous ∀
-- foo : v∀₁ (α ∷ β ∷ []) λ αs → P γ
-- foo : α → β → P γ
-- foo = vλ₁ λ hvec → ...

v∀₁ : ∀ {n}(αs : Vec₁ Set n) → (HVec αs → Set) → Set
v∀₁ []       f = f []
v∀₁ (α ∷ αs) f = (x : α) → v∀₁ αs λ xs → f (x ∷ xs)

_v→₁_ : ∀ {n} → Vec₁ Set n → Set → Set
_v→₁_ αs β = v∀₁ αs λ _ → β

vλ₁ : ∀ {n}{αs : Vec₁ Set n}{f}
    → ((xs : HVec αs) → f xs)
    → v∀₁ αs f
vλ₁ {αs = []}     f = f []
vλ₁ {αs = α ∷ αs} f = λ x → vλ₁ λ xs → f (x ∷ xs)

λv₁ : ∀ {n}{αs : Vec₁ Set n}{f}
    → v∀₁ αs f
    → ((xs : HVec αs) → f xs)
λv₁ f []       = f
λv₁ f (x ∷ xs) = λv₁ (f x) xs
