module DiDepCont where


infix 5 _▹_
data DiDepCont (Shape : Set)
               (Pos : (s : Shape) → Set)
               (Elt : (s : Shape) → (p : Pos s) → Set) : Set where
  _▹_ : (shape : Shape)
      → ((p : Pos shape) → Elt shape p)
      → DiDepCont Shape Pos Elt

fmap : ∀ {S P E₁ E₂}
     → (∀ {s p} → E₁ s p → E₂ s p)
     → DiDepCont S P E₁
     → DiDepCont S P E₂
fmap fe_ (s ▹ c_) = s ▹ λ p → fe c p

dimap : ∀ {S P₁ P₂ E₁ E₂}
      → (fp : ∀ {s} → P₂ s → P₁ s) -- contravariant!
      → (fe : ∀ {s p} → E₁ s (fp p) → E₂ s p)
      → DiDepCont S P₁ E₁
      → DiDepCont S P₂ E₂
dimap fp_ fe_ (s ▹ c_) = s ▹ λ p → fe c fp p

dismap : ∀ {S₁ S₂ P₁ P₂ E₁ E₂}
       → (fs : S₁ → S₂)
       → (fp : ∀ {s} → P₂ (fs s) → P₁ s) -- contravariant!
       → (fe : ∀ {s p} → E₁ s (fp p) → E₂ (fs s) p)
       → DiDepCont S₁ P₁ E₁
       → DiDepCont S₂ P₂ E₂
dismap fs fp_ fe_ (s ▹ c_) = fs s ▹ λ p → fe c fp p
