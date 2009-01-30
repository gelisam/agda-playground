module Monad where

open import Data.Function
open import Data.List hiding ([_]; _∈_)
open import Data.Product

infixr 4 _➝_
data Type : Set where
  ⊤ : Type
  _➝_ : Type → Type → Type

Ctx = List Type

infix 0 _∈_
-- Variables
data _∈_ : Type → Ctx → Set where
  vz : ∀ {Γ τ}
     → τ ∈ τ ∷ Γ

  vs : ∀ {Γ τ₁ τ₂}
     → τ₂ ∈ Γ
     → τ₂ ∈ τ₁ ∷ Γ

infix  2 _⊢_
infixr 3 ν_
infixl 3 _·_
infixr 2 ƛ_
-- Term
data _⊢_ : Ctx → Type → Set where
  tt  : ∀ {Γ}
      → Γ ⊢ ⊤

  ν_  : ∀ {Γ τ}
      → τ ∈ Γ
      → Γ ⊢ τ

  _·_ : ∀ {Γ τ₁ τ₂}
      → Γ ⊢ τ₁ ➝ τ₂
      → Γ ⊢ τ₁
      → Γ ⊢ τ₂

  ƛ_  : ∀ {Γ τ₁ τ₂}
      → τ₁ ∷ Γ ⊢ τ₂
      → Γ ⊢ τ₁ ➝ τ₂

record Kit (_◆_ : Ctx → Type → Set) : Set where
  field
    vr : ∀ {Γ τ}
       → τ ∈ Γ
       → Γ ◆ τ

    tm : ∀ {Γ τ}
       → Γ ◆ τ
       → Γ ⊢ τ

    wk : ∀ {Γ τ₁ τ₂}
       → Γ ◆ τ₁
       → (τ₂ ∷ Γ) ◆ τ₁

open Kit

lift : ∀ {_◆_ Γ Δ τ₁ τ₂}
     → Kit _◆_
     → (∀ {x} → x ∈ Γ → Δ ◆ x)
     → τ₂ ∈ τ₁ ∷ Γ
     → (τ₁ ∷ Δ) ◆ τ₂
lift k τ vz     = vr k vz
lift k τ (vs x) = wk k (τ x)

trav : ∀ {_◆_ Γ Δ τ}
     → Kit _◆_
     → (∀ {x} → x ∈ Γ → Δ ◆ x)
     → Γ ⊢ τ
     → Δ ⊢ τ
trav k τ tt        = tt
trav k τ (ν x)     = tm k (τ x)
trav k τ (e₁ · e₂) = trav k τ e₁ · trav k τ e₂
trav k τ (ƛ e)     = ƛ trav k (lift k τ) e

rename : ∀ {Γ Δ τ}
       → (∀ {x} → x ∈ Γ → x ∈ Δ)
       → Γ ⊢ τ
       → Δ ⊢ τ
rename ρ e = trav kit ρ e
  where
    kit = record
        { vr = id
        ; tm = ν_
        ; wk = vs
        }

substSim : ∀ {Γ Δ τ}
         → (∀ {x} → x ∈ Γ → Δ ⊢ x)
         → Γ ⊢ τ
         → Δ ⊢ τ
substSim σ e = trav kit σ e
  where
    kit = record
        { vr = ν_
        ; tm = id
        ; wk = rename vs
        }

subst : ∀ {Γ τ₁ τ₂}
      → τ₁ ∷ Γ ⊢ τ₂
      → Γ ⊢ τ₁
      → Γ ⊢ τ₂
subst {Γ} {τ₁} e₁ e₂ = substSim f e₁
  where
    f : ∀ {γ : Type}
      → γ ∈ τ₁ ∷ Γ
      → Γ ⊢ γ
    f vz     = e₂
    f (vs x) = ν x

data Val : {τ : Type} → [] ⊢ τ → Set where
  Val-tt : Val tt

  Val-ƛ : ∀ {σ τ} {e : σ ∷ [] ⊢ τ}
        → Val (ƛ e)

norm : ∀ {τ}
     → [] ⊢ τ
     → Σ ([] ⊢ τ) Val
norm tt = , Val-tt
norm (ν ())
norm (e₁ · e₂) with norm e₁
... | (ν ())      , _
... | (e₁' · e₂') , ()
... | (ƛ e₁')     , _  = norm (subst e₁' e₂')
  where
    e₂' = proj₁ (norm e₂)
norm (ƛ e) = , Val-ƛ {e = e}

-- infixl 1 _⟩⟩=_
-- codata Comp (α : Set) : Set1 where
--    return : α → Comp α
--    _⟩⟩=_  : ∀ {β} → Comp β → (β → Comp α) → Comp α

-- normComp : ∀ {τ}
--      → [] ⊢ τ
--      → Comp (Σ ([] ⊢ τ) Val)
-- normComp tt        ~ return (, Val-tt)
-- normComp (ν ())
-- normComp (e₁ · e₂) ~
--   normComp e₁ ⟩⟩= λ e₁' → 
--   normComp e₂ ⟩⟩= λ e₂' →
--   normComp' e₁' e₂'
--   where
--     normComp' : ∀ {τ₁ τ₂}
--               → Σ ([] ⊢ τ₁ ➝ τ₂) Val
--               → Σ ([] ⊢ τ₁) Val
--               → Comp (Σ ([] ⊢ τ₂) Val)
--     normComp' ((ν ())   , _ ) _
--     normComp' ((_ · _)  , ()) _
--     normComp' ((ƛ e₁'') , _ ) (e₂'' , _) ~ normComp (subst e₁'' e₂'')
-- normComp (ƛ e)     ~ return (, Val-ƛ {e = e})
