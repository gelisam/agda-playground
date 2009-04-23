module DiCont where


infix 5 _▹_
data DiCont (Shape : Set) (Pos : Shape → Set) (Elt : Shape → Set) : Set where
  _▹_ : (shape : Shape)
      → (Pos shape → Elt shape)
      → DiCont Shape Pos Elt

fmap : ∀ {S P α β}
     → (∀ {s} → α s → β s)
     → DiCont S P α
     → DiCont S P β
fmap f_ (s ▹ c_) = s ▹ λ p → f c p

cofmap : ∀ {S α β E}
       → (∀ {s} → β s → α s)
       → DiCont S α E
       → DiCont S β E
cofmap f_ (s ▹ c_) = s ▹ λ p → c f p

difmap : ∀ {S α β}
       → (∀ {s} → α s → β s)
       → (∀ {s} → β s → α s)
       → DiCont S α α
       → DiCont S β β
difmap f_ f⁻¹_ (s ▹ c_) = s ▹ λ p → f c f⁻¹ p
