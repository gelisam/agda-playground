module DiCont where


infix 5 _▹_
data DiCont (Shape : Set) (Pos : Shape → Set) (Elt : Shape → Set) : Set where
  _▹_ : (shape : Shape)
      → (Pos shape → Elt shape)
      → DiCont Shape Pos Elt

fmap : ∀ {S P α β}
     → (∀ {x} → α x → β x)
     → DiCont S P α
     → DiCont S P β
fmap f_ (x ▹ el_) = x ▹ λ p → f el p

cofmap : ∀ {S α β E}
       → (∀ {x} → β x → α x)
       → DiCont S α E
       → DiCont S β E
cofmap f_ (x ▹ el_) = x ▹ λ p → el f p

difmap : ∀ {S α β}
       → (∀ {x} → α x → β x)
       → (∀ {x} → β x → α x)
       → DiCont S α α
       → DiCont S β β
difmap f_ f⁻¹_ (x ▹ el_) = x ▹ λ p → f el f⁻¹ p
