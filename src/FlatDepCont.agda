module FlatDepCont where


infix 5 _▹_
data FlatDepCont (Shape : Set)
             (Pos : Set)
             (Elt : (p : Pos) → Set) : Set where
  _▹_ : (shape : Shape)
      → ((p : Pos) → Elt p)
      → FlatDepCont Shape Pos Elt

fmap : ∀ {S P α β}
     → (∀ {p} → α p → β p)
     → FlatDepCont S P α
     → FlatDepCont S P β
fmap f_ (s ▹ c_) = s ▹ λ p → f c p
