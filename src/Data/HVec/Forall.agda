module Data.HVec.Forall where
open import Data.Nat
open import Data.Vec1
open import Data.HVec
-- heterogenous ∀
-- foo : v∀ (α ∷ β ∷ []) λ αs → γ
-- foo : α → β → γ
-- foo = vλ λ hvec → ...

v∀ : ∀ {n}(αs : Vec₁ Set n) → (HVec αs → Set) → Set
v∀ []       f = f []
v∀ (α ∷ αs) f = (x : α) → v∀ αs λ xs → f (x ∷ xs)

_v→_ : ∀ {n} → Vec₁ Set n → Set → Set
_v→_ αs β = v∀ αs λ _ → β

vλ : ∀ {n}{αs : Vec₁ Set n}{f}
   → ((xs : HVec αs) → f xs)
   → v∀ αs f
vλ {αs = []}     f = f []
vλ {αs = α ∷ αs} f = λ x → vλ λ xs → f (x ∷ xs)

λv : ∀ {n}{αs : Vec₁ Set n}{f}
   → v∀ αs f
   → ((xs : HVec αs) → f xs)
λv f []       = f
λv f (x ∷ xs) = λv (f x) xs
