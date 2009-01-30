module Data.Fun.Type where
open import Data.List1
open import Data.HList
open import Data.Product1
open import Data.Product1.Exists
-- Reification of function types (α₁  → α₂ → ... → β)

infixr 7 _⇾_
infix 7 _$
data Type : Set → Set1 where
  _$  : ∀ α → Type α
  _⇾_ : ∀ α {β} → Type β → Type (α → β)

type : List₁ Set → Set → ∃₁₁ λ α → Type α
type []       β = β
                , β $
type (α ∷ αs) β = (α → proj₁₁₁ (type αs β))
                , (α ⇾ proj₁₁₂ (type αs β))

arg-t : ∀ {α} → Type α → List₁ Set
arg-t (_ $)   = []
arg-t (α ⇾ β) = α ∷ arg-t β

ret-t : ∀ {α} → Type α → Set
ret-t (α $)   = α
ret-t (α ⇾ β) = ret-t β

apply : ∀ {α} {α' : Type α} → α → HList (arg-t α') → ret-t α'
apply {α' = α $}   f []       = f
apply {α' = α ⇾ β} f (x ∷ xs) = apply (f x) xs
