module Data.Pat.Helper where
open import Data.List1
open import Data.HList
open import Data.Product1
open import Data.Pat
-- helper notation to create a Pat out of an ordinary function

infixr 7 _⇾_
data Type : Set → Set1 where
  #_  : (α : Set) → Type α
  _⇾_ : (α : Set) {β : Set} → Type β → Type (α → β)

private
  arg-t : {α : Set} → Type α → List₁ Set
  arg-t (# _)   = []
  arg-t (α ⇾ β) = α ∷ arg-t β

  ret-t : {α : Set} → Type α → Set
  ret-t (# α)   = α
  ret-t (α ⇾ β) = ret-t β

  apply : {α : Set} {α' : Type α} → α → HList (arg-t α') → ret-t α'
  apply {α' = # α}   f []       = f
  apply {α' = α ⇾ β} f (x ∷ xs) = apply (f x) xs

infix 6 _∶_
_∶_ : {α : Set} (p : α) (α' : Type α) → Pat (ret-t α')
_∶_ p α' = arg-t α' , apply p
