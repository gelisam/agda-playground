module Main where
open import Data.Fin hiding (#_)
open import Data.Vec1
open import Data.HList
open import Data.Product1
open import Data.Pat
open import Data.Pat.Helper
open import Data.Pat.Cover
open import Relation.Binary.PropositionalEquality


open import Data.Unit

-- case t : ⊤ of
--   box(. ⊤) ⇒ ...
case-⊤ : Case ⊤ 1
case-⊤ = tt ∶ # ⊤
       ∷ []

cover-⊤ : Cover case-⊤
cover-⊤ tt = (zero , []) , refl


open import Data.Function hiding (_∶_)

-- case n : α of
--   box(. U[.]) ⇒ ...
case-U : ∀ α → Case α 1
case-U α = id ∶ α ⇾ # α
         ∷ []

cover-U : ∀ {α} → Cover (case-U α)
cover-U x = (zero , x ∷ []) , refl


open import Data.Nat

-- case n : ℕ of
--   box(. zero) ⇒ ...
--   box(. suc U[.]) ⇒ ...
case-z-s : Case ℕ 2
case-z-s = zero ∶ # ℕ
         ∷ suc  ∶ ℕ ⇾ # ℕ
         ∷ []

cover-z-s : Cover case-z-s
cover-z-s zero    = (zero , []) , refl
cover-z-s (suc n) = (suc zero , n ∷ []) , refl


open import Data.Tree

-- case t : Tree α of
--   box(. Branch L[.] X[.] R[.]) ⇒ ...
--   box(. Leaf) ⇒ ...
case-branch-leaf : ∀ α → Case (Tree α) 2
case-branch-leaf α = Branch ∶ Tree α ⇾ α ⇾ Tree α ⇾ # Tree α
                   ∷ Leaf   ∶ # Tree α
                   ∷ []

cover-branch-leaf : ∀ {α} → Cover (case-branch-leaf α)
cover-branch-leaf (Branch l x r) = (zero , l ∷ x ∷ r ∷ []) , refl
cover-branch-leaf Leaf           = (suc zero , []) , refl


open import Data.Product

-- case p : α × β of
--   box(. U[.] , V[.]) ⇒ ...
case-U,V : (α β : Set) → Case (α × β) 1
case-U,V α β = _,_ ∶ α ⇾ β ⇾ # (α × β)
             ∷ []

cover-U,V : ∀ {α β} → Cover (case-U,V α β)
cover-U,V ( a , b ) = (zero , a ∷ b ∷ []) , refl
