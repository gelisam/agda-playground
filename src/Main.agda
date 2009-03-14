module Main where


open import Data.Function
open import Data.Unit using (⊤)
open import Data.Product


infixr 6 _→t_
data Type : Set where
  unit : Type
  _→t_  : (τ₁ τ₂ : Type) → Type 

⟦_⟧t : Type → Set
⟦ unit ⟧t = ⊤
⟦ τ₁ →t τ₂ ⟧t = ⟦ τ₁ ⟧t → ⟦ τ₂ ⟧t


infixl 5 _▸_
data Context : Set where
  ε   : Context
  _▸_ : Context → Type → Context

⟦_⟧c : Context → Set
⟦ ε ⟧c = ⊤
⟦ Γ ▸ τ ⟧c = ⟦ Γ ⟧c × ⟦ τ ⟧t


mutual
  infix 3 _⊦_
  infix 3 _⊦◇_
  infixl 4 _⋅_
  data _⊦_ : Context → Type → Set where
    tt  : ε ⊦ unit
    var : ∀ {Γ τ}
        → Γ ▸ τ ⊦ τ
    _⋅_ : ∀ {Γ τ₁ τ₂}
        → Γ ⊦◇ τ₁ →t τ₂
        → Γ ⊦◇ τ₁
        → Γ ⊦ τ₂
    ƛ   : ∀ {Γ τ₁ τ₂}
        → Γ ▸ τ₁ ⊦◇ τ₂
        → Γ ⊦ τ₁ →t τ₂
  
  infix 3 _≤_
  _≤_ : Context → Context → Set
  Γ ≤ Δ = ⟦ Δ ⟧c → ⟦ Γ ⟧c
  
  _⊦◇_ : Context → Type → Set
  Δ ⊦◇ τ = ∃ λ Γ → Γ ≤ Δ × Γ ⊦ τ


-- _≤_ is reflexive and transitive, so it's at least a preorder.
-- 
-- if it was antisymmetric (which it is if we use logical equivalence for equality),
-- it would be a partial order.
-- 
-- it's also monotonic and transitive. it there a special name for it?

reflexive : ∀ {Γ}
          → Γ ≤ Γ
reflexive = id

transitive : ∀ {Γ Δ Ψ}
           → Γ ≤ Δ
           →     Δ ≤ Ψ
           → Γ   ≤   Ψ
transitive f g = f ∘ g

monotonic : ∀ {Γ Δ τ}
          → Γ     ≤ Δ
          → Γ ▸ τ ≤ Δ ▸ τ
monotonic f x = f (proj₁ x) , proj₂ x

weaken : ∀ {Γ τ}
       → Γ ≤ Γ ▸ τ
weaken = proj₁

initial : ∀ {Γ}
        → ε ≤ Γ
initial x = _


mutual
  true-j : ∀ {Γ τ}
         → (j : Γ ⊦ τ)
         → ⟦ Γ ⟧c → ⟦ τ ⟧t
  true-j                tt         _        = _
  true-j                var       (eΓ , eτ) = eτ
  true-j {Γ}            (e₁ ⋅ e₂)  eΓ       = true-◇ {Γ} e₁ eΓ (true-◇ {Γ} e₂ eΓ)
  true-j {Γ} {τ₁ →t τ₂} (ƛ e)      eΓ       = λ eτ₁ → true-◇ {Γ ▸ τ₁} e (eΓ , eτ₁)
  
  true-◇ : ∀ {Δ τ}
         → (j : Δ ⊦◇ τ)
         → ⟦ Δ ⟧c → ⟦ τ ⟧t
  true-◇ (Γ , Γ≤Δ , j) = true-j j ∘ Γ≤Δ

-- here's how to add ((ƛ x → ...) tt) around a jugement j.
complexify : ∀ {Γ τ}
         → Γ ⊦ τ
         → Γ ⊦ τ
complexify {Γ} {τ} j = ◇ƛ ⋅ ◇tt where
  weaker-j : Γ ▸ unit ⊦◇ τ
  weaker-j = Γ , weaken {Γ} , j
  
  ◇ƛ : Γ ⊦◇ unit →t τ
  ◇ƛ = Γ , reflexive {Γ} , ƛ {Γ} weaker-j
  
  ◇tt : Γ ⊦◇ unit
  ◇tt = ε , initial {Γ} , tt

-- here's how to add ((ƛ x → ...) tt) around an opaque variable
-- having the same type as j.
simplify : ∀ {Γ τ}
         → Γ ⊦ τ
         → Γ ⊦ τ
simplify {Γ} {τ} j = ◇ƛ ⋅ ◇tt where
  ◇ƛ : Γ ⊦◇ unit →t τ
  ◇ƛ = ε ▸ unit →t τ , (λ eΓ → _ , λ _ → true-j j eΓ) , var
  
  ◇tt : Γ ⊦◇ unit
  ◇tt = ε , initial {Γ} , tt
