module CoCont (Shape : Set) (Pos : Shape → Set) where


infix 5 _▹_
data CoCont (α : Set) : Set where
  _▹_ : (shape : Shape)
      → (α → Pos shape)
      → CoCont α

cofmap : ∀ {α β}
       → (β → α)
       → CoCont α
       → CoCont β
cofmap f_ (x ▹ el_) = x ▹ λ p → el f p
