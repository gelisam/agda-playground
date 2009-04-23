module CoCont where


infix 5 _▹_
data CoCont (Shape : Set) (Pos : Set) (Elt : Shape → Set) : Set where
  _▹_ : (shape : Shape)
      → (Pos → Elt shape)
      → CoCont Shape Pos Elt

cofmap : ∀ {S E α β}
       → (β → α)
       → CoCont S α E
       → CoCont S β E
cofmap f_ (x ▹ el_) = x ▹ λ p → el f p
