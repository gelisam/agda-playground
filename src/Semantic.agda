module Semantic where


open import Context
open import Data.Unit using (⊤)
open import Data.Product


⟦_⟧t : Type → Set
⟦ unit ⟧t = ⊤
⟦ τ₁ →t τ₂ ⟧t = ⟦ τ₁ ⟧t → ⟦ τ₂ ⟧t

⟦_⟧c : Context → Set
⟦ ε ⟧c = ⊤
⟦ Γ ▸ τ ⟧c = ⟦ Γ ⟧c × ⟦ τ ⟧t

infix 3 _≤_
_≤_ : Context → Context → Set
Γ ≤ Δ = ⟦ Δ ⟧c → ⟦ Γ ⟧c

import Jugement
open Jugement _≤_
open import Data.Function

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
         → (j : Γ ⊦ τ term)
         → ⟦ Γ ⟧c → ⟦ τ ⟧t
  true-j                tt         _        = _
  true-j                var       (eΓ , eτ) = eτ
  true-j {Γ}            (e₁ ⋅ e₂)  eΓ       = true-◇ {Γ} e₁ eΓ (true-◇ {Γ} e₂ eΓ)
  true-j {Γ} {τ₁ →t τ₂} (ƛ e)      eΓ       = λ eτ₁ → true-◇ {Γ ▸ τ₁} e (eΓ , eτ₁)
  
  true-◇ : ∀ {Δ τ}
         → (j : Δ ⊦◇ τ term)
         → ⟦ Δ ⟧c → ⟦ τ ⟧t
  true-◇ (Γ / Γ≤Δ ⊦ j) = true-j j ∘ Γ≤Δ

-- here's how to add ((ƛ x → ...) tt) around a jugement j.
complexify : ∀ {Γ τ}
         → Γ ⊦ τ term
         → Γ ⊦ τ term
complexify {Γ} {τ} j = ◇ƛ ⋅ ◇tt where
  weaker-j : Γ ▸ unit ⊦◇ τ term
  weaker-j = Γ / weaken {Γ} ⊦ j
  
  ◇ƛ : Γ ⊦◇ unit →t τ term
  ◇ƛ = Γ / reflexive {Γ} ⊦ ƛ {Γ} weaker-j
  
  ◇tt : Γ ⊦◇ unit term
  ◇tt = ε / initial {Γ} ⊦ tt

-- here's how to add ((ƛ x → ...) tt) around an opaque variable
-- having the same type as j.
simplify : ∀ {Γ τ}
         → Γ ⊦ τ term
         → Γ ⊦ τ term
simplify {Γ} {τ} j = ◇ƛ ⋅ ◇tt where
  ◇ƛ : Γ ⊦◇ unit →t τ term
  ◇ƛ = ε ▸ unit →t τ / (λ eΓ → _ , λ _ → true-j j eΓ) ⊦ var
  
  ◇tt : Γ ⊦◇ unit term
  ◇tt = ε / initial {Γ} ⊦ tt


import Substitution
open Substitution _≤_
  (λ {Γ}     → reflexive  {Γ})
  (λ {Γ Δ Ψ} → transitive {Γ} {Δ} {Ψ})
  (λ {Γ Δ τ} → monotonic  {Γ} {Δ} {τ})
  (λ {Γ   τ} → weaken     {Γ}     {τ})
