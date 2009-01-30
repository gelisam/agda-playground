module Main where
open import Data.Fin
open import Data.Vec1
open import Data.HList
open import Data.Fun.Type
open import Data.Pat
open import Data.Pat.Helper
open import Data.Pat.Cover


open import Data.Unit

-- view t : ⊤ of
--   box(. ⊤) ⇒ ...
view-⊤ : View ⊤ 1
view-⊤ = tt ∶ ⊤ $
       ∷ []

cover-⊤ : Cover view-⊤
cover-⊤ tt = cover-with view-⊤ (# 0)


open import Data.Function hiding (_∶_)

-- view n : α of
--   box(. U[.]) ⇒ ...
view-U : ∀ α → View α 1
view-U α = id ∶ α ⇾ α $
         ∷ []

cover-U : ∀ α → Cover (view-U α)
cover-U α x = cover-with (view-U α) (# 0) x


open import Data.Nat

-- view n : ℕ of
--   box(. zero) ⇒ ...
--   box(. suc U[.]) ⇒ ...
view-z-s : View ℕ 2
view-z-s = zero ∶ ℕ $
         ∷ suc  ∶ ℕ ⇾ ℕ $
         ∷ []

cover-z-s : Cover view-z-s
cover-z-s zero    = cover-with view-z-s (# 0)
cover-z-s (suc n) = cover-with view-z-s (# 1) n


open import Data.Tree

-- view t : Tree α of
--   box(. Branch L[.] X[.] R[.]) ⇒ ...
--   box(. Leaf) ⇒ ...
view-B-L : ∀ α → View (Tree α) 2
view-B-L α = Branch ∶ Tree α ⇾ α ⇾ Tree α ⇾ Tree α $
                   ∷ Leaf   ∶ Tree α $
                   ∷ []

cover-B-L : ∀ α → Cover (view-B-L α)
cover-B-L α (Branch l x r) = cover-with (view-B-L α) (# 0) l x r
cover-B-L α Leaf           = cover-with (view-B-L α) (# 1)


open import Data.Product

-- view p : α × β of
--   box(. U[.] , V[.]) ⇒ ...
view-U,V : ∀ α β → View (α × β) 1
view-U,V α β = _,_ ∶ α ⇾ β ⇾ (α × β) $
             ∷ []

cover-U,V : ∀ α β → Cover (view-U,V α β)
cover-U,V α β (a , b) = cover-with (view-U,V α β) (# 0) a b
