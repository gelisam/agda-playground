module Subset where

open import Data.List using (List; []; _∷_; _++_; [_])

open import Elem

module _ {A : Set} where
  data _⊆_ : List A → List A → Set where
    []
      : [] ⊆ []
    yes∷_
      : ∀ {x xs xys}
      → xs ⊆ xys
      → x ∷ xs ⊆ x ∷ xys
    no∷_
      : ∀ {y xs xys}
      → xs ⊆ xys
      → xs ⊆ y ∷ xys
  infix 4 _⊆_

  emptySubset
    : ∀ {xys : List A}
    → [] ⊆ xys
  emptySubset {[]}
    = []
  emptySubset {_ ∷ xys}
    = no∷ (emptySubset {xys})

  fullSubset
    : ∀ {xs : List A}
    → xs ⊆ xs
  fullSubset {[]}
    = []
  fullSubset {_ ∷ xs}
    = yes∷ (fullSubset {xs})

  _++[yes]
    : ∀ {x : A} {xs xys}
    → xs ⊆ xys
    → (xs ++ [ x ]) ⊆ (xys ++ [ x ])
  [] ++[yes]
    = yes∷ []
  (yes∷ subset) ++[yes]
    = yes∷ (subset ++[yes])
  (no∷ subset) ++[yes]
    = no∷ (subset ++[yes])

  _++[no]
    : ∀ {x : A} {xs xys}
    → xs ⊆ xys
    → xs ⊆ (xys ++ [ x ])
  [] ++[no]
    = no∷ []
  (yes∷ subset) ++[no]
    = yes∷ (subset ++[no])
  (no∷ subset) ++[no]
    = no∷ (subset ++[no])

  weakenElem
    : ∀ {x : A} {xs xys}
    → xs ⊆ xys
    → Elem x xs
    → Elem x xys
  weakenElem (yes∷_ _) Here
    = Here
  weakenElem (yes∷ xs) (There i)
    = There (weakenElem xs i)
  weakenElem (no∷ xs) i
    = There (weakenElem xs i)
