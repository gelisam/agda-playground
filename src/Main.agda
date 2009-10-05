module Main where

open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import OpenM


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
  countV eq? x (var y) with eq? x y
  ... | yes _              = 1
  ... | no  _              = 0
  countV eq? x (app e₁ e₂) = countV eq? x e₁ +
                                 countV eq? x e₂
  countV eq? x (lam e)     = countV (weaken-eq eq?) (weaken-var x) e
  
  var₁ : Ctx 1
  var₁ = hoas-var λ _ x
       → x
  
  term₁ : Term (Ctx 1)
  term₁ = hoas λ _ x
        → app (lam (hoas λ _ y
                         → weaken x))
              (app x x)
  
  assert₁ : countV open-eq var₁ term₁ ≡ 3
  assert₁ = refl
