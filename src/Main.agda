module Main where


infixr 2 _⇾_
data Type : Set where
  Unit : Type
  _⇾_  : Type → Type → Type

infixl 1 _▸_
data Ctx : Set where
  ε   : Ctx
  _▸_ : Ctx → Type → Ctx

infix 0 _⊦_term 
infixl 1 _⋅_
data _⊦_term (Γ : Ctx) : Type → Set where
  unit : Γ ⊦ Unit    term
  _⋅_  : ∀ {τ₁ τ₂}
       → Γ ⊦ τ₁ ⇾ τ₂ term
       → Γ ⊦ τ₁      term
       → Γ ⊦      τ₂ term
  ƛ    : ∀ {τ₁ τ₂}
       → Γ ▸ τ₁ ⊦ τ₂ term
       → Γ ⊦ τ₁ ⇾ τ₂ term
