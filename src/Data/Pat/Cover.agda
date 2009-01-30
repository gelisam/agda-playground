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

-- a list of pattern-matching attempts which might not cover all cases
Case : Set → ℕ → Set1
Case α n = Vec₁ (Pat α) n

private
  construct : {α : Set}{n : ℕ}
            → (case : Case α n)
            → (Σ₀₁ (Fin n) λ i → HList (pat-dom (lookup i case)))
            → α
  construct case i,xs = pat-apply p xs where
    i = proj₀₁₁ i,xs
    p = lookup i case
    xs = proj₀₁₂ i,xs
  
-- a Case which does cover all cases
Cover : {α : Set}{n : ℕ} → Case α n → Set1
Cover case = Surjective₁₀ (construct case)
