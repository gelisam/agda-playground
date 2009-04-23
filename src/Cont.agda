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
fmap f_ (s ▹ c_) = s ▹ λ p → f c p

cofmap : ∀ {S α β E}
       → (∀ {s} → β s → α s)
       → Cont S α E
       → Cont S β E
cofmap f_ (s ▹ c_) = s ▹ λ p → c f p
