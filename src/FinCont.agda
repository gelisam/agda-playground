open import Data.Nat
open import Data.Fin

module FinCont (Shape : Set) (Pos : Shape → ℕ) where


infix 5 _▹_
data FinCont (α : Set) : Set where
  _▹_ : (shape : Shape)
      → (Fin (Pos shape) → α)
      → FinCont α

fmap : ∀ {α β}
     → (α → β)
     → FinCont α
     → FinCont β
fmap f_ (s ▹ c_) = s ▹ λ p → f c p
