module FlatCont where


infix 5 _▹_
data FlatCont (Shape : Set) (Pos : Set) (Elt : Set) : Set where
  _▹_ : (shape : Shape)
      → (Pos → Elt)
      → FlatCont Shape Pos Elt

fmap : ∀ {S P α β}
     → (α → β)
     → FlatCont S P α
     → FlatCont S P β
fmap f_ (s ▹ c_) = s ▹ λ p → f c p

cofmap : ∀ {S α β E}
       → (β → α)
       → FlatCont S α E
       → FlatCont S β E
cofmap f_ (s ▹ c_) = s ▹ λ p → c f p

difmap : ∀ {S α β}
       → (α → β)
       → (β → α)
       → FlatCont S α α
       → FlatCont S β β
difmap f_ f⁻¹_ (s ▹ c_) = s ▹ λ p → f c f⁻¹ p
