module Main where
open import Data.Fin
open import Data.Vec1
open import Data.HList
open import Data.Fun.Type
open import Data.Pat
open import Data.Pat.Helper
open import Data.Pat.Cover


open import Data.Unit

-- case t : ⊤ of
--   box(. ⊤) ⇒ ...
case-⊤ : Case ⊤ 1
case-⊤ = tt ∶ ⊤ $
       ∷ []

cover-⊤ : Cover case-⊤
cover-⊤ tt = cover-with case-⊤ (# 0)


open import Data.Function hiding (_∶_)

-- case n : α of
--   box(. U[.]) ⇒ ...
case-U : ∀ α → Case α 1
case-U α = id ∶ α ⇾ α $
         ∷ []

cover-U : ∀ α → Cover (case-U α)
cover-U α x = cover-with (case-U α) (# 0) x


open import Data.Nat

-- case n : ℕ of
--   box(. zero) ⇒ ...
--   box(. suc U[.]) ⇒ ...
case-z-s : Case ℕ 2
case-z-s = zero ∶ ℕ $
         ∷ suc  ∶ ℕ ⇾ ℕ $
         ∷ []

cover-z-s : Cover case-z-s
cover-z-s zero    = cover-with case-z-s (# 0)
cover-z-s (suc n) = cover-with case-z-s (# 1) n


open import Data.Tree

-- case t : Tree α of
--   box(. Branch L[.] X[.] R[.]) ⇒ ...
--   box(. Leaf) ⇒ ...
case-B-L : ∀ α → Case (Tree α) 2
case-B-L α = Branch ∶ Tree α ⇾ α ⇾ Tree α ⇾ Tree α $
                   ∷ Leaf   ∶ Tree α $
                   ∷ []

cover-B-L : ∀ α → Cover (case-B-L α)
cover-B-L α (Branch l x r) = cover-with (case-B-L α) (# 0) l x r
cover-B-L α Leaf           = cover-with (case-B-L α) (# 1)


open import Data.Product

-- case p : α × β of
--   box(. U[.] , V[.]) ⇒ ...
case-U,V : (α β : Set) → Case (α × β) 1
case-U,V α β = _,_ ∶ α ⇾ β ⇾ (α × β) $
             ∷ []

cover-U,V : ∀ α β → Cover (case-U,V α β)
cover-U,V α β (a , b) = cover-with (case-U,V α β) (# 0) a b
