module Elem where

open import Data.List using (List; []; _∷_; _++_; [_])


module _ {A : Set} where
  data Elem : A → List A → Set where
    Here : ∀ {x xs} → Elem x (x ∷ xs)
    There : ∀ {x y xs} → Elem x xs → Elem x (y ∷ xs)