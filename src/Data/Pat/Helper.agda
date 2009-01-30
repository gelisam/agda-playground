module Data.Pat.Helper where
open import Data.Product1
open import Data.Fun.Type
open import Data.Fun.Helper public hiding (_∶_)
open import Data.Pat
-- helper notation to create a Pat out of an ordinary function

infix 6 _∶_
_∶_ : ∀ {α} (p : α) (α' : Type α) → Pat (ret-t α')
_∶_ p α' = arg-t α' , apply p
