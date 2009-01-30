module Data.Pat.Cover where
open import Data.Nat
open import Data.Vec1
open import Data.Fin
open import Data.HList
open import Data.Pat
open import Data.Product1
open import Data.Product1.Times
open import Data.Product1.Exists
open import Relation.Unary.Surjective1

open import Data.HList.Forall1
open import Relation.Binary.PropositionalEquality

-- a list of pattern-matching attempts which might not cover all views
View : Set → ℕ → Set1
View α n = Vec₁ (Pat α) n

private
  construct : ∀ {α n}
            → (view : View α n)
            → (∃₀₁ λ i → HList (pat-dom (lookup i view)))
            → α
  construct view i,xs = pat-apply p xs where
    i = proj₀₁₁ i,xs
    p = lookup i view
    xs = proj₀₁₂ i,xs
  
-- a View which does cover all views
Cover : ∀ {α n} → View α n → Set1
Cover view = Surjective₁₀ (construct view)


-- helper for implementing (Cover view)
cover-with : ∀ {α n}
           → (view : View α (suc n))
           → (j : Fin (suc n))
           → l∀₁ (pat-dom (lookup j view))
             λ xs → ∃₁₀
             λ i,xs →
               construct view i,xs
             ≡ construct view (j , xs)
cover-with view j = lλ₁ (pat-dom (lookup j view))
                    λ xs → (j , xs) , refl
