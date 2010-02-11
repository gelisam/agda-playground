module Main where

open import Data.Nat
open import Data.Fin
open import Data.Vec1
open import Relation.Binary.PropositionalEquality1 hiding (subst; cong₂)
open import Relation.Binary.PropositionalEquality2


data Lift (a : Set) : Set1 where
  lift : a → Lift a

infixr 0 _⇾_
data Type (Γ : ℕ) : Set1 where
  ref : Fin Γ → Type Γ
  con : Set → Type Γ
  _⇾_ : Type Γ → Type Γ → Type Γ
  all : Type (suc Γ) → Type Γ

⟦_⊦_⟧ : ∀ {Γ}
    → Vec₁ Set Γ
    → Type Γ
    → Set1
⟦ xs ⊦ ref i ⟧ = Lift (lookup i xs)
⟦ xs ⊦ con a ⟧ = Lift a
⟦ xs ⊦ a ⇾ b ⟧ = ⟦ xs ⊦ a ⟧ → ⟦ xs ⊦ b ⟧
⟦ xs ⊦ all b ⟧ = (a : Set) → ⟦ a ∷ xs ⊦ b ⟧

⟦_⟧ : Type 0 → Set1
⟦ a ⟧ = ⟦ [] ⊦ a ⟧

data Hyp : Set1 where
  hyp : {a a′ : Set}
      → (Lift a → Lift a′)
      → Hyp

dom : Hyp → Set
dom (hyp {a₁} {a₂} fa) = a₁

img : Hyp → Set
img (hyp {a₁} {a₂} fa) = a₂

fun : (h : Hyp)
    → Lift (dom h)
    → Lift (img h)
fun (hyp fa) = fa

doms : ∀ {Γ}
     → Vec₁ Hyp Γ
     → Vec₁ Set Γ
doms = map dom

imgs : ∀ {Γ}
     → Vec₁ Hyp Γ
     → Vec₁ Set Γ
imgs = map img

lem :  ∀ {Γ xs}
    →  {f  : Hyp → Set}
    →  (i  : Fin Γ)
    →  Lift (f     (lookup i xs))
    ≡₂ Lift (lookup i (map f xs))
lem {zero}  {[]}     ()
lem {suc Γ} {x ∷ xs} zero    = refl
lem {suc Γ} {x ∷ xs} (suc i) = lem i

infix 0 _⊦free-theorem
_⊦free-theorem : ∀ {Γ}
               → (xs : Vec₁ Hyp Γ)
               → (t : Type Γ)
               → ⟦ doms xs ⊦ t ⟧
               → ⟦ imgs xs ⊦ t ⟧
               → Set1
_⊦free-theorem xs (ref i) a₁ a₂ = Lift (fa a₁ ≡₁ a₂) where
  f : Lift (dom (lookup i xs))
    → Lift (img (lookup i xs))
  f = fun (lookup i xs)
  
  prf :  (Lift (dom  (lookup i xs)) → Lift (img  (lookup i xs)))
      ≡₂ (Lift (lookup i (doms xs)) → Lift (lookup i (imgs xs)))
  prf = cong₂ (λ a b → a → b) (lem i) (lem i)
  
  fa : Lift (lookup i (doms xs))
     → Lift (lookup i (imgs xs))
  fa = subst prf f
_⊦free-theorem xs (con a) a₁ a₂ = Lift (a₁ ≡₁ a₂)
_⊦free-theorem xs (a ⇾ b) f₁ f₂ = (a₁ : ⟦ doms xs ⊦ a ⟧)
                                → (a₂ : ⟦ imgs xs ⊦ a ⟧)
                                → (xs ⊦free-theorem) a     a₁      a₂
                                → (xs ⊦free-theorem) b (f₁ a₁) (f₂ a₂)
_⊦free-theorem xs (all b) f₁ f₂ = (a₁ : Set)
                                → (a₂ : Set)
                                → (fa : Lift a₁ → Lift a₂)
                                → (hyp fa ∷ xs ⊦free-theorem) b (f₁ a₁) (f₂ a₂)

free-theorem : (t : Type 0)
             → ⟦ t ⟧ → ⟦ t ⟧ → Set1
free-theorem t x y = ([] ⊦free-theorem) t x y

postulate parametricity : ∀ t
                        → (x : ⟦ t ⟧)
                        → free-theorem t x x

App : Type 1
App = con ℕ
    ⇾ (ref zero ⇾ ref zero)
    ⇾ (ref zero ⇾ ref zero)
app : ⟦ all App ⟧
app a (lift zero)    f x = x
app a (lift (suc i)) f x = f (app a (lift i) f x)

app-param : (a₁ a₂ : Set)
          → (fa : Lift a₁ → Lift a₂)
          → (i₁ i₂ : Lift ℕ)
          → Lift (i₁ ≡₁ i₂)
          → (g₁ : Lift a₁ → Lift a₁)
          → (g₂ : Lift a₂ → Lift a₂)
          → (f∥g : (x₁ : Lift a₁)
                 → (x₂ : Lift a₂)
                 → Lift (fa     x₁  ≡₁    x₂)
                 → Lift (fa (g₁ x₁) ≡₁ g₂ x₂))
          → (x₁ : Lift a₁)
          → (x₂ : Lift a₂)
          → Lift (fa               x₁  ≡₁              x₂)
          → Lift (fa (app a₁ i₁ g₁ x₁) ≡₁ app a₂ i₂ g₂ x₂)
app-param = parametricity (all App) app
