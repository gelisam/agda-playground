module Main where
open import Data.List1
open import Data.List1.In
open import Data.List1.All2
open import Data.HList
open import Data.Product1
open import Relation.Binary.PropositionalEquality
open import Beluga

open import Data.Unit
open import Data.Nat
open import Data.Function hiding (_∶_)
open import Data.Tree
open import Data.Product

-- case t : ⊤ of
--   box(. ⊤) ⇒ ...
case-⊤ : Case ⊤
case-⊤ = tt ∶ # ⊤
       ∷ []

cover-⊤ : Cover case-⊤
cover-⊤ tt = (_
             , here
             , [])
           , refl

-- case n : α of
--   box(. U[.]) ⇒ ...
case-U : (α : Set) → Case α
case-U α = id ∶ α ⇾ # α
         ∷ []

cover-U : {α : Set} → Cover (case-U α)
cover-U x = (_
            , here
            , x ∷ [])
          , refl

-- case n : ℕ of
--   box(. zero) ⇒ ...
--   box(. suc U[.]) ⇒ ...
case-z-s : Case ℕ
case-z-s = zero ∶ # ℕ
         ∷ suc  ∶ ℕ ⇾ # ℕ
         ∷ []

cover-z-s : Cover case-z-s
cover-z-s zero    = (_
                    , here
                    , [])
                  , refl
cover-z-s (suc n) = (_
                    , there here
                    , n ∷ [])
                  , refl

-- case t : Tree α of
--   box(. Branch L[.] X[.] R[.]) ⇒ ...
--   box(. Leaf) ⇒ ...
case-branch-leaf : (α : Set) → Case (Tree α)
case-branch-leaf α = Branch ∶ Tree α ⇾ α ⇾ Tree α ⇾ # Tree α
                   ∷ Leaf   ∶ # Tree α
                   ∷ []

cover-branch-leaf : {α : Set} → Cover (case-branch-leaf α)
cover-branch-leaf (Branch l x r) = (_
                                   , here
                                   , l ∷ x ∷ r ∷ [])
                                 , refl
cover-branch-leaf Leaf           = (_
                                   , there here
                                   , [])
                                 , refl

-- case p : α × β of
--   box(. U[.] , V[.]) ⇒ ...
case-U,V : (α β : Set) → Case (α × β)
case-U,V α β = _,_ ∶ α ⇾ β ⇾ # (α × β)
             ∷ []

cover-U,V : {α β : Set} → Cover (case-U,V α β)
cover-U,V ( a , b ) = (_
                      , here
                      , a ∷ b ∷ [])
                    , refl
