module Pair where

open import Coinduction

open import Desc


_×_ : DelayDesc → DelayDesc → DelayDesc
ret        × b = b
arg A tA d × b = arg A tA d′ where
  d′ : A → ∞₁ DelayDesc
  d′ a = ♯₁ ♭₁ (d a) × b


_,_ : ∀ {A B} → ⟦ A ⟧ → ⟦ B ⟧ → ⟦ A × B ⟧
_,_ {ret}        ret       b = b
_,_ {arg A tA d} (arg a x) b = arg a (x , b)

proj₁ : ∀ {A B} → ⟦ A × B ⟧ → ⟦ A ⟧
proj₁ {ret}        _         = ret
proj₁ {arg A tA d} (arg a x) = arg a (proj₁ x)

proj₂ : ∀ {A B} → ⟦ A × B ⟧ → ⟦ B ⟧
proj₂ {ret}        b         = b
proj₂ {arg A tA d} (arg a x) = proj₂ {♭₁ (d a)} x

unpair : ∀ {A B} → {C : Set} → ⟦ A × B ⟧ → (⟦ A ⟧ → ⟦ B ⟧ → C) → C
unpair {A} {B} ab f = f (proj₁ {A} {B} ab) (proj₂ {A} {B} ab)