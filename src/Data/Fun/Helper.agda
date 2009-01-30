module Data.Fun.Helper where
open import Data.Fun
open import Data.Fun.Type
-- helper notation to create a Fun out of an ordinary function

infix 6 _∶_
_∶_ : ∀ {α} (p : α) (α' : Type α) → Fun (arg-t α') (ret-t α')
_∶_ p α' = apply p
