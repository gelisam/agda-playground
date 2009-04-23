module Cont where


infix 5 _▹_
data Cont (Shape : Set) (Pos : Shape → Set) (Elt : Set) : Set where
  _▹_ : (shape : Shape)
      → (Pos shape → Elt)
      → Cont Shape Pos Elt

fmap : ∀ {S P α β}
     → (α → β)
     → Cont S P α
     → Cont S P β
fmap f_ (x ▹ el_) = x ▹ λ p → f el p
