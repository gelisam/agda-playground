module Data.Pat.Case where
open import Data.Fin
open import Data.Vec1 renaming (map to map₁₁)
open import Data.HList
open import Data.HList.Forall
open import Data.HVec
open import Data.HVec.Forall
open import Data.Product1
open import Data.Pat
open import Data.Pat.Cover
open import Relation.Binary.PropositionalEquality1

private
  branch : {α : Set} → Set → Pat α → Set
  branch β p = pat-dom p l→ β

  lem : ∀ {α β n}(i : Fin n)(v : View α n)
      → lookup i (map₁₁ (branch β) v) ≡₁ (pat-dom (lookup i v) l→ β)
  lem zero    (x ∷ xs) = refl
  lem (suc i) (x ∷ xs) = lem i xs

case : ∀ {α β n}{v : View α n} → α → Cover v → map₁₁ (branch β) v v→ β
case {α} {β} {n} {v} x c =
    vλ {αs = map₁₁ (branch β) v}
     λ bs → λl (at i bs) xs
  where
    i,xs = proj₁₀₁ (c x)
    i  = proj₀₁₁ i,xs
    xs = proj₀₁₂ i,xs
    at : (i : Fin n)
       → HVec n (map₁₁ (branch β) v)
       → pat-dom (lookup i v)
      l→ β
    at i bs = subst (lem i v) (hlookup i bs)
