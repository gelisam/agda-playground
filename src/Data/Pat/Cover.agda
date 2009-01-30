module Data.Pat.Cover where
open import Data.List1
open import Data.List1.In
open import Data.HList
open import Data.Pat
open import Data.Product1
open import Data.Product1.Times
open import Data.Product1.Exists
open import Relation.Unary.Surjective1


-- a list of pattern-matching attempts which might not cover all cases
Case : Set → Set1
Case α = List₁ (Pat α)

-- a Case which does cover all cases
Cover : {α : Set} → Case α → Set1
Cover {α} case = Surjective₁₀ construct where
  construct : (∃₁₁ λ p → p ∈₁ case ×₁₁ HList (pat-dom p)) → α
  construct p,∈,xs = pat-apply p xs where
    p = proj₁₁₁ p,∈,xs
    ∈,xs = proj₁₁₂ p,∈,xs
    xs = proj₁₁₂ ∈,xs
