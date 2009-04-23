module DepCont where


infix 5 _▹_
data DepCont (Shape : Set)
             (Pos : Set)
             (Elt : (p : Pos) → Set) : Set where
  _▹_ : (shape : Shape)
      → ((p : Pos) → Elt p)
      → DepCont Shape Pos Elt

fmap : ∀ {S P α β}
     → (∀ {p} → α p → β p)
     → DepCont S P α
     → DepCont S P β
fmap f_ (s ▹ c_) = s ▹ λ p → f c p
