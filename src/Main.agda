module Main where

open import Data.Unit
open import Data.Vec
open import Data.Nat
open import Data.Sum
open import Relation.Binary.PropositionalEquality1
open import Relation.Binary.HeterogeneousEquality


-- for type constructors
tNeutral : {A : Set}
         → (A → Set)
         → Set
tNeutral P = ∀ {x y}
           → P x ≡₁ P y
           →   x ≅ y

cong-type : ∀ {A B}
          → {a : A}
          → {b : B}
          → a ≅ b
          → A ≡₁ B
cong-type refl = refl

cong-arg : ∀ {A P}
         → tNeutral P
         → {x : A}{xs : P x}
         → {y : A}{ys : P y}
         → xs ≅ ys
         → x ≅ y
cong-arg neutral prf = neutral (cong-type prf)


dependent-subst : {A : Set}
                → {B : A → Set}
                → tNeutral B
                → (P : ∀ x → B x → Set)
                → {x₁ : A}{y₁ : B x₁}
                → {x₂ : A}{y₂ : B x₂}
                → y₁ ≅ y₂
                → P x₁ y₁
                → P x₂ y₂
dependent-subst nB P prf p = lemma (cong-arg nB prf) prf p where
  lemma : ∀ {x₁ x₂ y₁ y₂}
        → x₁ ≅ x₂
        → y₁ ≅ y₂
        → P x₁ y₁
        → P x₂ y₂
  lemma refl refl p = p

dependent-cong : {A : Set}
               → {B : A → Set}
               → tNeutral B
               → {C : ∀ x → B x → Set}
               → (f : ∀ x y → C x y)
               → {x₁ : A}{y₁ : B x₁}
               → {x₂ : A}{y₂ : B x₂}
               → y₁ ≅ y₂
               → f x₁ y₁
               ≅ f x₂ y₂
dependent-cong nB f prf = lemma (cong-arg nB prf) prf where
  lemma : ∀ {x₁ x₂ y₁ y₂}
        → x₁ ≅ x₂
        → y₁ ≅ y₂
        → f x₁ y₁
        ≅ f x₂ y₂
  lemma refl refl = refl


List = Vec ℕ
nList : tNeutral List
nList refl = refl

list-subst : (P : ∀ x → List x → Set)
           → {x₁ : ℕ}{y₁ : List x₁}
           → {x₂ : ℕ}{y₂ : List x₂}
           → y₁ ≅ y₂
           → P x₁ y₁
           → P x₂ y₂
list-subst = dependent-subst nList

list-cong : {c : ∀ x → List x → Set}
          → (f : ∀ x y → c x y)
          → {x₁ : ℕ}{y₁ : List x₁}
          → {x₂ : ℕ}{y₂ : List x₂}
          → y₁ ≅ y₂
          → f x₁ y₁
          ≅ f x₂ y₂
list-cong = dependent-cong nList


-- for value contructors
vNeutral : {A : Set}
         → {B : A → Set}
         → (∀ x → B x)
         → Set
vNeutral f = ∀ {x y}
           → f x ≅ f y
           →   x ≅ y

-- ...I'm sure it must be useful too, but I can't find a good example.

nSuc : vNeutral suc
nSuc refl = refl
