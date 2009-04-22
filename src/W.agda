module W where

open import Data.Empty
open import Data.Unit

-- W types, the Well-ordering type constructor for Martin-Löf type
-- theory.  W types are capable of representing inductive data types
-- in a generic way.  M types are their coinductive duals.

-- The intuition is that α represents the "set of constructor labels"
-- for the type and ⟦_⟧ reoresents the decoder for the labels into
-- concrete sets in the universe.
data W (α : Set) (⟦_⟧ : α → Set) : Set where
  sup : (a : α) (f : ⟦ a ⟧ → W α ⟦_⟧) → W α ⟦_⟧

-- elimination of a W type (i.e., fold)
wrec : ∀ {α ⟦_⟧} {γ : W α ⟦_⟧ → Set}
     → (a : W α ⟦_⟧)
     → ((y : α) → (z : ⟦ y ⟧ → W α ⟦_⟧) → (u : (x : ⟦ y ⟧) → γ (z x)) → γ (sup y z))
     → γ a
wrec {γ = γ} (sup d e) b = b d e (λ x → wrec {γ = γ} (e x) b)
