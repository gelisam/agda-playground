module CoCont where


infix 5 _▹_
data CoCont (Shape : Set) (Pos : Set) (Elt : Shape → Set) : Set where
  _▹_ : (shape : Shape)
      → (Pos → Elt shape)
      → CoCont Shape Pos Elt

fmap : ∀ {S P E₁ E₂}
     → (∀ {s} → E₁ s → E₂ s)
     → CoCont S P E₁
     → CoCont S P E₂
fmap fe_ (s ▹ c_) = s ▹ λ p → fe c p

pmap : ∀ {S P₁ P₂ E}
       → (P₂ → P₁) -- contravariant!
       → CoCont S P₁ E
       → CoCont S P₂ E
pmap fp_ (s ▹ c_) = s ▹ λ p → c fp p

dimap : ∀ {S P₁ P₂ E₁ E₂}
      → (P₂ → P₁) -- contravariant!
      → (∀ {s} → E₁ s → E₂ s)
      → CoCont S P₁ E₁
      → CoCont S P₂ E₂
dimap fp_ fe_ (s ▹ c_) = s ▹ λ p → fe c fp p

dismap : ∀ {S₁ S₂ P₁ P₂ E₁ E₂}
       → (fs : S₁ → S₂)
       → (P₂ → P₁) -- contravariant!
       → (∀ {s} → E₁ s → E₂ (fs s))
       → CoCont S₁ P₁ E₁
       → CoCont S₂ P₂ E₂
dismap fs fp_ fe_ (s ▹ c_) = fs s ▹ λ p → fe c fp p
