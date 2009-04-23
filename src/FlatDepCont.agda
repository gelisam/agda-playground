module FlatDepCont where


infix 5 _▹_
data FlatDepCont (Shape : Set)
             (Pos : Set)
             (Elt : (p : Pos) → Set) : Set where
  _▹_ : (shape : Shape)
      → ((p : Pos) → Elt p)
      → FlatDepCont Shape Pos Elt

fmap : ∀ {S P E₁ E₂}
     → (∀ {p} → E₁ p → E₂ p)
     → FlatDepCont S P E₁
     → FlatDepCont S P E₂
fmap fe_ (s ▹ c_) = s ▹ λ p → fe c p

dimap : ∀ {S P₁ P₂ E₁ E₂}
      → (fp : P₂ → P₁) -- contravariant!
      → (∀ {p} → E₁ (fp p) → E₂ p)
      → FlatDepCont S P₁ E₁
      → FlatDepCont S P₂ E₂
dimap fp_ fe_ (s ▹ c_) = s ▹ λ p → fe c fp p

smap : ∀ {S₁ S₂ P E}
     → (S₁ → S₂)
     → FlatDepCont S₁ P E
     → FlatDepCont S₂ P E
smap fs (s ▹ c) = fs s ▹ c

dismap : ∀ {S₁ S₂ P₁ P₂ E₁ E₂}
       → (S₁ → S₂)
       → (fp : P₂ → P₁) -- contravariant!
       → (∀ {p} → E₁ (fp p) → E₂ p)
       → FlatDepCont S₁ P₁ E₁
       → FlatDepCont S₂ P₂ E₂
dismap fs fp_ fe_ (s ▹ c_) = fs s ▹ λ p → fe c fp p
