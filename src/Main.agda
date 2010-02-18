module Main where

open import Data.Empty
open import Data.Sum
open import Data.Function
open import Relation.Nullary

¬¬ : Set → Set
¬¬ A = ¬ ¬ A

_↯_ : ∀ {A B} → A → ¬ A → B
_↯_ {A} {B} a ¬a = ⊥-elim {B} $ ¬a a

return : ∀ {A} → A → ¬¬ A
return a ¬a = a ↯ ¬a

_⟫=_ : ∀ {A B : Set} → ¬¬ A → (A → ¬¬ B) → ¬¬ B
_⟫=_ ¬¬a f ¬b = ¬¬a λ a → f a ¬b

em : ∀ {A} → ¬¬(A ⊎ ¬ A)
em ¬[A+¬A] = ¬[A+¬A] $ inj₂ λ a → ¬[A+¬A] $ inj₁ a

dneg : ∀ {A} → ¬¬(¬¬ A → A)
dneg {A} = em ⟫=
         [ (λ  a → return λ ¬¬a → a)
         , (λ ¬a → return λ ¬¬a → ¬a ↯ ¬¬a)
         ]

peirce : ∀ {A B : Set} → ¬¬(((A → B) → A) → A)
peirce = em ⟫=
       [ (λ  a → return λ [a⇾b]⇾a → a)
       , (λ ¬a → return λ [a⇾b]⇾a → [a⇾b]⇾a λ a → a ↯ ¬a)
       ]
