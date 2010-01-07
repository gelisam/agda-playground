module Delay where

open import Coinduction


data Delay (A : Set) : Set where
  now   : A →           Delay A
  later : ∞ (Delay A) → Delay A

data Terminates {A : Set} : Delay A → Set where
  now   : ∀ {x} →                Terminates (now x)
  later : ∀ {d} → Terminates d → Terminates (later (♯ d))

undelay : ∀ {A} d → Terminates {A} d → A
undelay .(now x)       (now {x})     = x
undelay .(later (♯ d)) (later {d} t) = undelay d t
