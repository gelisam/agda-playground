module OpenM where

open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality


hoas-var : ∀ {Γ}
         → (body : ∀ A → Γ ⊎ A → Γ ⊎ A)
         → Γ ⊎ ⊤
hoas-var body = body ⊤ (inj₂ _)

Ctx : ℕ → Set
Ctx zero    = ⊥
Ctx (suc n) = Ctx n ⊎ ⊤

swap-last : ∀ {Γ A B}
          → (Γ ⊎ A) ⊎ B
          → (Γ ⊎ B) ⊎ A
swap-last (inj₁ (inj₁ x)) = inj₁ (inj₁ x)
swap-last (inj₁ (inj₂ a)) = inj₂ a
swap-last (inj₂ b)        = inj₁ (inj₂ b)


weaken-map : ∀ {Γ₁ Γ₂}
           → (Γ₁ → Γ₂)
           → Γ₁ ⊎ ⊤
           → Γ₂ ⊎ ⊤
weaken-map f (inj₁ x) = inj₁ (f x)
weaken-map f (inj₂ _) = inj₂ _

weaken-var : ∀ {Γ}
           → Γ
           → Γ ⊎ ⊤
weaken-var = inj₁

weaken-sub′ : (Term : Set → Set)
           → ∀ {Γ₁ Γ₂}
           → (Γ₂ ⊎ ⊤ → Term (Γ₂ ⊎ ⊤))
           → (Term Γ₂ → Term (Γ₂ ⊎ ⊤))
           → (Γ₁ → Term Γ₂)
           → Γ₁ ⊎ ⊤
           → Term (Γ₂ ⊎ ⊤)
weaken-sub′ Term var weaken sub (inj₁ x) = weaken (sub x)
weaken-sub′ Term var weaken sub (inj₂ _) = var (inj₂ _)

weaken-eq : ∀ {Γ}
          → Decidable {Γ} _≡_
          → Decidable {Γ ⊎ ⊤} _≡_
weaken-eq {Γ} eq? (inj₁ x) (inj₁ y) with eq? x y
weaken-eq {Γ} eq? (inj₁ x) (inj₁ .x) | yes refl = yes refl
weaken-eq {Γ} eq? (inj₁ x) (inj₁ y)  | no  ¬x≡y = no (↯ x y ¬x≡y) where
  ↯ : (u v : Γ)
    → ¬ (u ≡ v)
    → _≡_ {Γ ⊎ ⊤} (inj₁ u) (inj₁ v)
    → ⊥
  ↯ u .u prf refl = prf refl
weaken-eq {Γ} eq? (inj₁ x) (inj₂ _) = no λ()
weaken-eq {Γ} eq? (inj₂ _) (inj₁ y) = no λ()
weaken-eq {Γ} eq? (inj₂ _) (inj₂ _) = yes (cong inj₂ refl)


closed-eq : Decidable {⊥} _≡_
closed-eq () ()

open-eq : ∀ {n}
        → Decidable {Ctx n} _≡_
open-eq {zero}  = closed-eq
open-eq {suc n} = weaken-eq open-eq


record Open : Set₁ where
  field
    Term       : Set → Set
    var        : ∀ {Γ} → Γ → Term Γ
    rename     : ∀ {Γ₁ Γ₂}
               → (Γ₁ → Γ₂)
               → Term Γ₁
               → Term Γ₂
    weaken     : ∀ {Γ A}
               → Term Γ
               → Term (Γ ⊎ A)
    substitute : ∀ {Γ₁ Γ₂}
               → (Γ₁ → Term Γ₂)
               → Term Γ₁
               → Term Γ₂
  
  hoas : ∀ {Γ}
       → (body : ∀ A → Term (Γ ⊎ A) → Term (Γ ⊎ A))
       → Term (Γ ⊎ ⊤)
  hoas body = body ⊤ (var (inj₂ _))
  
  _[_] : ∀ {Γ₁ Γ₂}
       → Term Γ₁
       → (Γ₁ → Term Γ₂)
       → Term Γ₂
  e [ σ ] = substitute σ e
  
  weaken-sub : ∀ {Γ₁ Γ₂} 
             → (Γ₁ → Term Γ₂)
             → Γ₁ ⊎ ⊤
             → Term (Γ₂ ⊎ ⊤)
  weaken-sub = weaken-sub′ Term var weaken
