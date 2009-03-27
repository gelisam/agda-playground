module Context.Syntax where

open import Data.Fin
open import Context


infix 5 _!!_
_!!_ : ∀ {n}
     → Ctx n
     → Fin n
     → Type
_!!_ = lookup-ctx
