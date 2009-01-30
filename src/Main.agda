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
^⊤ : Cover ⊤
^⊤ = covers case downward complete
  where
    case = tt ∶ # ⊤
         ∷ []

    downward : Downward case
    downward = [] ∷ []

    complete : Complete case
    complete tt = (_
                  , here
                  , [])
                , refl

-- case n : ℕ of
--   box(. U[.]) ⇒ ...
^U : Cover ℕ
^U ~ covers case downward complete
  where
    case = id ∶ ℕ ⇾ # ℕ
         ∷ []

    downward : Downward case
    downward = (^U ∷ [])
             ∷ []

    complete : Complete case
    complete n = (_
                 , here
                 , n ∷ [])
               , refl

-- case n : ℕ of
--   box(. zero) ⇒ ...
--   box(. suc U[.]) ⇒ ...
^z-s : Cover ℕ
^z-s ~ covers case downward complete
  where
    case = zero ∶ # ℕ
         ∷ suc  ∶ ℕ ⇾ # ℕ
         ∷ []

    downward : Downward case
    downward = []
             ∷ (^z-s ∷ [])
             ∷ []

    complete : Complete case
    complete zero    = (_
                       , here
                       , [])
                     , refl
    complete (suc n) = (_
                       , there here
                       , n ∷ [])
                     , refl

-- case t : Tree α of
--   box(. Branch L[.] X[.] R[.]) ⇒ ...
--   box(. Leaf) ⇒ ...
^branch-leaf : {α : Set} -> Cover α → Cover (Tree α)
^branch-leaf {α} ^α ~ covers case downward complete
  where

    case = Branch ∶ Tree α ⇾ α ⇾ Tree α ⇾ # Tree α
         ∷ Leaf   ∶ # Tree α
         ∷ []

    downward : Downward case
    downward = (^branch-leaf ^α ∷ ^α ∷ ^branch-leaf ^α ∷ [])
             ∷ []
             ∷ []

    complete : Complete case
    complete (Branch l x r) = (_
                              , here
                              , l ∷ x ∷ r ∷ [])
                            , refl
    complete Leaf           = (_
                              , there here
                              , [])
                            , refl

-- case p : α × β of
--   box(. U[.] , V[.]) ⇒ ...
^U,V : {α β : Set} → Cover α → Cover β → Cover (α × β)
^U,V {α} {β} ↓α ↓β ~ covers case downward complete
  where
    pair = _,_

    case = pair ∶ α ⇾ β ⇾ # (α × β)
         ∷ []

    downward : Downward case
    downward = (↓α ∷ ↓β ∷ [])
             ∷ []

    complete : Complete case
    complete ( a , b ) = (_
                         , here
                         , a ∷ b ∷ [])
                         , refl
