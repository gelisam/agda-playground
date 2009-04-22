module Meta.Cont (Shape : Set) (Pos : Shape → Set) where

open import Data.Empty
open import Data.Product
open import W


-- yes, you can model Containers using W types.
-- but it's rather boring.

Cont : Set → Set
Cont α = W (∃ λ shape → Pos shape → α) ⟦_⟧ where
  ⟦_⟧ : (∃ λ shape → Pos shape → α) → Set
  ⟦ _ ⟧ = ⊥

infix 5 _▹_
_▹_ : ∀ {α}
    → (shape : Shape)
    → (Pos shape → α)
    → Cont α
_▹_ x el = sup (x , el) λ()

fmap : ∀ {α β}
     → (α → β)
     → Cont α
     → Cont β
fmap f_ (sup x▹el _) = x▹fel where
  x     = proj₁ x▹el
  el_   = proj₂ x▹el
  x▹fel = x ▹ λ p → f el p
