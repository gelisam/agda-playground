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

-- a list of pattern-matching attempts which might not cover all cases
Case : Set → ℕ → Set1
Case α n = Vec₁ (Pat α) n

private
  construct : ∀ {α n}
            → (case : Case α n)
            → (∃₀₁ λ i → HList (pat-dom (lookup i case)))
            → α
  construct case i,xs = pat-apply p xs where
    i = proj₀₁₁ i,xs
    p = lookup i case
    xs = proj₀₁₂ i,xs
  
-- a Case which does cover all cases
Cover : ∀ {α n} → Case α n → Set1
Cover case = Surjective₁₀ (construct case)


-- helper for implementing (Cover case)
cover-with : ∀ {α n}
           → (case : Case α (suc n))
           → (j : Fin (suc n))
           → l∀₁ (pat-dom (lookup j case))
             λ xs → ∃₁₀
             λ i,xs →
               construct case i,xs
             ≡ construct case (j , xs)
cover-with case j = lλ₁ (pat-dom (lookup j case))
                    λ xs → (j , xs) , refl
