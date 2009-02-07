module Data.Pat.Case where

open import Data.Function hiding (_∶_)

open import Data.Fun.Type
open import Data.Pat.Helper

-- lookup zero (map₁₁ (branch ℕ) (id ∶ ℕ ⇾ ℕ $ ∷ []))

open import Data.Nat
open import Data.Fin
open import Data.Vec1 renaming (map to map₁₁)
open import Data.HList
open import Data.HList.Forall
open import Data.HVec
open import Data.HVec.Forall
open import Data.Product1
open import Data.Product1.Exists
open import Data.Pat
open import Data.Pat.Cover
open import Relation.Binary.PropositionalEquality1

branch : {α : Set} → Set → Pat α → Set
branch β p = ℕ → β -- pat-dom p l→ β

lem : ∀ {α β n}(i : Fin n)(v : View α n)
    → lookup i (map₁₁ (branch β) v) ≡₁ (ℕ → β)
lem zero    (x ∷ xs) = refl
lem (suc i) (x ∷ xs) = lem i xs

construct : ∀ {α n}
          → (view : View α n)
          → (∃₀₁ λ i → HList (pat-dom (lookup i view)))
          → α
construct view i,xs = pat-apply p xs where
  i = proj₀₁₁ i,xs
  p = lookup i view
  xs = proj₀₁₂ i,xs

case : ∀ {α β n}{v : View α n} → α → Cover v → map₁₁ (branch β) v v→ β
case {α} {β} {n} {v} x c =
    vλ {αs = map₁₁ (branch β) v}
     λ bs → subst (lem i v) (hlookup i bs) zero
  where
    i,xs = proj₁₀₁ (c x)
    i  : Fin n
    i  = proj₀₁₁ i,xs
    xs : HList (pat-dom (lookup i v))
    xs = proj₀₁₂ i,xs
