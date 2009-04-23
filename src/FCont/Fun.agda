module FCont.Fun where

open import Data.Unit
open import Data.Fin
open import FCont

-- with FCont, the encoding is impossible
-- because we don't know how many inhabitants α has

-- Fun : Set → Set → Set
-- Fun α β = FCont ⊤ (λ _ → ?) β
