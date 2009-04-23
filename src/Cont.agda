module Cont where


infix 5 _▹_
data Cont (Shape : Set) (Pos : Shape → Set) (Elt : Set) : Set where
  _▹_ : (shape : Shape)
      → (Pos shape → Elt)
      → Cont Shape Pos Elt

fmap : ∀ {S P E₁ E₂}
     → (E₁ → E₂)
     → Cont S P E₁
     → Cont S P E₂
fmap fe_ (s ▹ c_) = s ▹ λ p → fe c p

pmap : ∀ {S P₁ P₂ E}
       → (∀ {s} → P₂ s → P₁ s) -- contravariant!
       → Cont S P₁ E
       → Cont S P₂ E
pmap fp_ (s ▹ c_) = s ▹ λ p → c fp p

dimap : ∀ {S P₁ P₂ E₁ E₂}
      → (∀ {s} → P₂ s → P₁ s) -- contravariant!
      → (E₁ → E₂)
      → Cont S P₁ E₁
      → Cont S P₂ E₂
dimap fp_ fe_ (s ▹ c_) = s ▹ λ p → fe c fp p

dismap : ∀ {S₁ S₂ P₁ P₂ E₁ E₂}
       → (fs : S₁ → S₂)
       → (∀ {s} → P₂ (fs s) → P₁ s) -- contravariant!
       → (fe : E₁ → E₂)
       → Cont S₁ P₁ E₁
       → Cont S₂ P₂ E₂
dismap fs fp_ fe_ (s ▹ c_) = fs s ▹ λ p → fe c fp p
