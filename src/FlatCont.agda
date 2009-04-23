module FlatCont where


infix 5 _▹_
data FlatCont (Shape : Set) (Pos : Set) (Elt : Set) : Set where
  _▹_ : (shape : Shape)
      → (Pos → Elt)
      → FlatCont Shape Pos Elt

fmap : ∀ {S P E₁ E₂}
     → (E₁ → E₂)
     → FlatCont S P E₁
     → FlatCont S P E₂
fmap fe_ (s ▹ c_) = s ▹ λ p → fe c p

pmap : ∀ {S P₁ P₂ E}
       → (P₂ → P₁) -- contravariant!
       → FlatCont S P₁ E
       → FlatCont S P₂ E
pmap fp_ (s ▹ c_) = s ▹ λ p → c fp p

dimap : ∀ {S P₁ P₂ E₁ E₂}
      → (P₂ → P₁) -- contravariant!
      → (E₁ → E₂)
      → FlatCont S P₁ E₁
      → FlatCont S P₂ E₂
dimap fp_ fe_ (s ▹ c_) = s ▹ λ p → fe c fp p

smap : ∀ {S₁ S₂ P E}
     → (S₁ → S₂)
     → FlatCont S₁ P E
     → FlatCont S₂ P E
smap fs (s ▹ c) = fs s ▹ c

dismap : ∀ {S₁ S₂ P₁ P₂ E₁ E₂}
       → (S₁ → S₂)
       → (P₂ → P₁) -- contravariant!
       → (E₁ → E₂)
       → FlatCont S₁ P₁ E₁
       → FlatCont S₂ P₂ E₂
dismap fs fp_ fe_ (s ▹ c_) = fs s ▹ λ p → fe c fp p
