module Main where

open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality


data Term (Γ : Set) : Set where
  var : Γ → Term Γ
  app : Term Γ → Term Γ → Term Γ
  lam : Term (Γ ⊎ ⊤) → Term Γ

hoas : ∀ {Γ}
     → (body : ∀ A → Term (Γ ⊎ A) → Term (Γ ⊎ A))
     → Term (Γ ⊎ ⊤)
hoas body = body ⊤ (var (inj₂ _))

-- fmap
rename : ∀ {Γ₁ Γ₂}
       → (Γ₁ → Γ₂)
       → Term Γ₁
       → Term Γ₂
rename {Γ₁} {Γ₂} f (var x)     = var (f x)
rename {Γ₁} {Γ₂} f (app e₁ e₂) = app (rename f e₁)
                                     (rename f e₂)
rename {Γ₁} {Γ₂} f (lam e)     = lam (rename f' e) where
  f' : Γ₁ ⊎ ⊤ → Γ₂ ⊎ ⊤
  f' (inj₁ x) = inj₁ (f x)
  f' (inj₂ _) = inj₂ _

swap-last : ∀ {Γ A B}
          → (Γ ⊎ A) ⊎ B
          → (Γ ⊎ B) ⊎ A
swap-last (inj₁ (inj₁ x)) = inj₁ (inj₁ x)
swap-last (inj₁ (inj₂ a)) = inj₂ a
swap-last (inj₂ b)        = inj₁ (inj₂ b)

weaken : ∀ {Γ A}
       → Term Γ
       → Term (Γ ⊎ A)
weaken {Γ} {A} (var x)     = var (inj₁ x)
weaken {Γ} {A} (app e₁ e₂) = app (weaken e₁)
                                 (weaken e₂)
weaken {Γ} {A} (lam e)     = lam (rename swap-last (weaken e))

_[_] : ∀ {Γ₁ Γ₂}
     → Term Γ₁
     → (Γ₁ → Term Γ₂)
     → Term Γ₂
_[_] {Γ₁} {Γ₂} (var x)     σ = σ x
_[_] {Γ₁} {Γ₂} (app e₁ e₂) σ = app (e₁ [ σ ])
                                   (e₂ [ σ ])
_[_] {Γ₁} {Γ₂} (lam e)     σ = lam (e [ σ' ]) where
  σ' : Γ₁ ⊎ ⊤ → Term (Γ₂ ⊎ ⊤)
  σ' (inj₁ x) = weaken (σ x)
  σ' (inj₂ _) = var (inj₂ _)


countV : ∀ {Γ}
       → Decidable {Γ} _≡_
       → Γ
       → Term Γ
       → ℕ
countV {Γ} eq? x (var y)     with eq? x y
... | yes _ = 1
... | no  _ = 0
countV {Γ} eq? x (app e₁ e₂) = countV eq? x e₁ +
                               countV eq? x e₂
countV {Γ} eq? x (lam e)     = countV eq?' (inj₁ x) e where
  eq?' : Decidable {Γ ⊎ ⊤} _≡_
  eq?' (inj₁ x) (inj₁ y) with eq? x y
  eq?' (inj₁ x) (inj₁ .x) | yes refl = yes refl
  eq?' (inj₁ x) (inj₁ y)  | no  ¬x≡y = no (↯ x y ¬x≡y) where
    ↯ : (u v : Γ)
      → ¬ (u ≡ v)
      → _≡_ {Γ ⊎ ⊤} (inj₁ u) (inj₁ v)
      → ⊥
    ↯ u .u prf refl = prf refl
  eq?' (inj₁ x) (inj₂ _) = no λ()
  eq?' (inj₂ _) (inj₁ y) = no λ()
  eq?' (inj₂ _) (inj₂ _) = yes (cong inj₂ refl)
