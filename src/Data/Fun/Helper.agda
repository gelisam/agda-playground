module Data.Fun.Helper where
open import Data.List1
open import Data.HList
open import Data.Fun
-- helper notation to create a Fun out of an ordinary function

infixr 7 _⇾_
infix 7 _$
data Type : Set → Set1 where
  _$  : ∀ α → Type α
  _⇾_ : ∀ α {β} → Type β → Type (α → β)

arg-t : ∀ {α} → Type α → List₁ Set
arg-t (_ $)   = []
arg-t (α ⇾ β) = α ∷ arg-t β

ret-t : ∀ {α} → Type α → Set
ret-t (α $)   = α
ret-t (α ⇾ β) = ret-t β

apply : ∀ {α} {α' : Type α} → α → HList (arg-t α') → ret-t α'
apply {α' = α $}   f []       = f
apply {α' = α ⇾ β} f (x ∷ xs) = apply (f x) xs

infix 6 _∶_
_∶_ : ∀ {α} (p : α) (α' : Type α) → Fun (arg-t α') (ret-t α')
_∶_ p α' = apply p
