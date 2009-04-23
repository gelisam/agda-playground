module DiDepCont where


infix 5 _▹_
data DiDepCont (Shape : Set)
               (Pos : (s : Shape) → Set)
               (Elt : (s : Shape) → (p : Pos s) → Set) : Set where
  _▹_ : (shape : Shape)
      → ((p : Pos shape) → Elt shape p)
      → DiDepCont Shape Pos Elt

fmap : ∀ {S P α β}
     → (∀ {s p} → α s p → β s p)
     → DiDepCont S P α
     → DiDepCont S P β
fmap f_ (s ▹ c_) = s ▹ λ p → f c p
