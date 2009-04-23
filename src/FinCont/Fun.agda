module FinCont.Fun where

open import Data.Unit
open import Data.Fin
open import FinCont

-- with FinCont, the encoding is impossible
-- because we don't know how many inhabitants α has

-- Fun : Set → Set → Set
-- Fun α β = FinCont ⊤ (λ _ → ?) β
