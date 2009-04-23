open import Data.Nat
open import Data.Fin

module FCont (Shape : Set) (Pos : Shape → ℕ) where


infix 5 _▹_
data FCont (α : Set) : Set where
  _▹_ : (shape : Shape)
      → (Fin (Pos shape) → α)
      → FCont α

fmap : ∀ {α β}
     → (α → β)
     → FCont α
     → FCont β
fmap f_ (x ▹ el_) = x ▹ λ p → f el p
