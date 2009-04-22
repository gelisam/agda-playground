module Cont (Shape : Set) (Pos : Shape → Set) where


infix 5 _▹_
data Cont (α : Set) : Set where
  _▹_ : (shape : Shape)
      → (Pos shape → α)
      → Cont α

fmap : ∀ {α β}
     → (α → β)
     → Cont α
     → Cont β
fmap f_ (x ▹ el_) = x ▹ λ p → f el p
