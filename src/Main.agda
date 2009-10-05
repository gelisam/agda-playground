module Main where

open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality


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
  

weaken-map : ∀ {Γ₁ Γ₂}
           → (Γ₁ → Γ₂)
           → Γ₁ ⊎ ⊤
           → Γ₂ ⊎ ⊤
weaken-map f (inj₁ x) = inj₁ (f x)
weaken-map f (inj₂ _) = inj₂ _

weaken-sub : (Term : Set → Set)
           → ∀ {Γ₁ Γ₂}
           → (Γ₂ ⊎ ⊤ → Term (Γ₂ ⊎ ⊤))
           → (Term Γ₂ → Term (Γ₂ ⊎ ⊤))
           → (Γ₁ → Term Γ₂)
           → Γ₁ ⊎ ⊤
           → Term (Γ₂ ⊎ ⊤)
weaken-sub Term var weaken sub (inj₁ x) = weaken (sub x)
weaken-sub Term var weaken sub (inj₂ _) = var (inj₂ _)

swap-last : ∀ {Γ A B}
          → (Γ ⊎ A) ⊎ B
          → (Γ ⊎ B) ⊎ A
swap-last (inj₁ (inj₁ x)) = inj₁ (inj₁ x)
swap-last (inj₁ (inj₂ a)) = inj₂ a
swap-last (inj₂ b)        = inj₁ (inj₂ b)

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


-- m4 macros to simplify the task of implementing rename etc

define(`rename_t', `∀ {Γ₁ Γ₂} → (Γ₁ → Γ₂) → $1 Γ₁ → $1 Γ₂')
define(`rename_v', `var ($2 $3)')
define(`rename_w', `(rename (weaken-map $2) $3)')

define(`weaken_t', `∀ {Γ A} → $1 Γ → $1 (Γ ⊎ A)')
define(`weaken_v', `var (inj₁ $2)')
define(`weaken_w', `(rename swap-last (weaken $2))')

define(`substitute_t', `∀ {Γ₁ Γ₂} → (Γ₁ → $1 Γ₂) → $1 Γ₁ → $1 Γ₂')
define(`substitute_v', `$2 $3')
define(`substitute_w', `(substitute (weaken-sub $1 var weaken $2) $3)')


module Lambda where
  data Term (Γ : Set) : Set where
    var : Γ → Term Γ
    app : Term Γ → Term Γ → Term Γ
    lam : Term (Γ ⊎ ⊤) → Term Γ

  -- fmap
  rename : rename_t(Term)
  rename f (var x)     = rename_v(Term, f, x)
  rename f (app e₁ e₂) = app (rename f e₁)
                             (rename f e₂)
  rename f (lam e)     = lam rename_w(Term, f, e)

  weaken : weaken_t(Term)
  weaken (var x)     = weaken_v(Term, x)
  weaken (app e₁ e₂) = app (weaken e₁)
                           (weaken e₂)
  weaken (lam e)     = lam weaken_w(Term, e)

  substitute : substitute_t(Term)
  substitute σ (var x)     = substitute_v(Term, σ, x)
  substitute σ (app e₁ e₂) = app (substitute σ e₁)
                                 (substitute σ e₂)
  substitute σ (lam e)     = lam substitute_w(Term, σ, e)
  
  Open-Term : Open
  Open-Term = record
            { Term       = Term
            ; var        = var
            ; rename     = rename
            ; weaken     = weaken
            ; substitute = substitute
            }
  open Open Open-Term hiding (Term; var; rename; weaken; substitute)

  
  countV : ∀ {Γ}
         → Decidable {Γ} _≡_
         → Γ
         → Term Γ
         → ℕ
  countV {Γ} eq? x (var y) with eq? x y
  ... | yes _ = 1
  ... | no  _ = 0
  countV {Γ} eq? x (app e₁ e₂) = countV eq? x e₁ +
                                 countV eq? x e₂
  countV {Γ} eq? x (lam e)     = countV (weaken-eq eq?) (inj₁ x) e
