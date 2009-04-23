open import Data.Nat
open import Data.Fin

module FinCont where


infix 5 _▹_
data FinCont (Shape : Set) (Pos : Shape → ℕ) (Elt : Set) : Set where
  _▹_ : (shape : Shape)
      → (Fin (Pos shape) → Elt)
      → FinCont Shape Pos Elt

fmap : ∀ {S P E₁ E₂}
     → (E₁ → E₂)
     → FinCont S P E₁
     → FinCont S P E₂
fmap fe_ (s ▹ c_) = s ▹ λ p → fe c p

pmap : ∀ {S P₁ P₂ E}
       → (∀ {s} → Fin (P₂ s) → Fin (P₁ s)) -- contravariant!
       → FinCont S P₁ E
       → FinCont S P₂ E
pmap fp_ (s ▹ c_) = s ▹ λ p → c fp p

dimap : ∀ {S P₁ P₂ E₁ E₂}
      → (∀ {s} → Fin (P₂ s) → Fin (P₁ s)) -- contravariant!
      → (E₁ → E₂)
      → FinCont S P₁ E₁
      → FinCont S P₂ E₂
dimap fp_ fe_ (s ▹ c_) = s ▹ λ p → fe c fp p

dismap : ∀ {S₁ S₂ P₁ P₂ E₁ E₂}
       → (fs : S₁ → S₂)
       → (∀ {s} → Fin (P₂ (fs s)) → Fin (P₁ s)) -- contravariant!
       → (fe : E₁ → E₂)
       → FinCont S₁ P₁ E₁
       → FinCont S₂ P₂ E₂
dismap fs fp_ fe_ (s ▹ c_) = fs s ▹ λ p → fe c fp p
