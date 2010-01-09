module Pair.Unordered where

open import Data.Empty
open import Coinduction
open import Relation.Binary.PropositionalEquality1 renaming (sym to sym₁; cong to cong₁₁)
-- open import Relation.Binary.HeterogeneousEquality

open import Refl
open import Total
open import Desc
open import Pair


data &Tag : Set where
  eq : &Tag
  lt : &Tag

total-&Tag : Total &Tag
total-&Tag = record
           { compare = compare
           ; valid   = valid
           } where
  compare : (x y : &Tag) → Compare x y
  compare eq eq = eq _
  compare eq lt = lt _ _
  compare lt eq = gt _ _
  compare lt lt = eq _
  
  valid : (x y : &Tag) → compare x y ≡ uncompare (compare y x)
  valid eq eq = refl
  valid eq lt = refl
  valid lt eq = refl
  valid lt lt = refl

&_ : DelayDesc → DelayDesc
& ret = ret
& arg A tA d = arg &Tag total-&Tag case-tag where
  case-tag : &Tag → ∞₁ DelayDesc
  case-tag eq = ♯₁ arg A tA λ a
              → ♯₁ & ♭₁ (d a)
  case-tag lt = ♯₁ arg A tA λ x
              → ♯₁ arg A tA λ y
              → ♯₁ arg (Total.compare tA x y ≡ lt x y) total-≡ λ _
              → ♯₁ ♭₁ (d x) × ♭₁ (d y)

drop-order : ∀ {A} → ⟦ A ⟧ → ⟦ A ⟧ → ⟦ & A ⟧
drop-order {ret} ret ret = ret
drop-order {arg A tA d} (arg x u) (arg y v) with inspect (Total.compare tA x y)
... | lt .x .y with-≡ p = arg lt (arg x (arg y (arg q (u , v)))) where q = sym p
... | gt .x .y with-≡ p = arg lt (arg y (arg x (arg q (v , u)))) where q = Total.gt-lt tA (sym p)
drop-order {arg A tA d} (arg .a u) (arg .a v) | eq a with-≡ p
         = arg eq (arg a (drop-order u v))

drop-order-commutes : ∀ {A} x y
                    →  drop-order {A} x y
                    ≡₁ drop-order {A} y x
drop-order-commutes {ret} ret ret = refl
drop-order-commutes {arg A tA d} (arg x u) (arg y v) with inspect (Total.compare tA x y)
                                                        | inspect (Total.compare tA y x)
... | lt .x .y with-≡ p | lt .y .x with-≡ q = ⊥-elim (Total.lt-lt tA x y (sym p) (sym q))
... | gt .x .y with-≡ p | gt .y .x with-≡ q = ⊥-elim (Total.gt-gt tA x y (sym p) (sym q))
... | lt .x .y with-≡ p | gt .y .x with-≡ q = cong₀₁ (λ r → arg lt (arg x (arg y (arg r (u , v))))) ≡-always-≡
... | gt .x .y with-≡ p | lt .y .x with-≡ q = cong₀₁ (λ r → arg lt (arg y (arg x (arg r (v , u))))) ≡-always-≡
drop-order-commutes {arg A tA d} (arg .a u) (arg .a v) | eq a with-≡ p | lt .a .a with-≡ q = ⊥-elim (Total.eq-lt tA a (sym q))
drop-order-commutes {arg A tA d} (arg .a u) (arg .a v) | eq a with-≡ p | gt .a .a with-≡ q = ⊥-elim (Total.eq-gt tA a (sym q))
drop-order-commutes {arg A tA d} (arg .a u) (arg .a v) | lt .a .a with-≡ p | eq a with-≡ q = ⊥-elim (Total.eq-lt tA a (sym p))
drop-order-commutes {arg A tA d} (arg .a u) (arg .a v) | gt .a .a with-≡ p | eq a with-≡ q = ⊥-elim (Total.eq-gt tA a (sym p))
drop-order-commutes {arg A tA d} (arg .a u) (arg .a v) | eq .a with-≡ p | eq a with-≡ q
                  = cong₁₁ (λ x → arg eq (arg a x)) (drop-order-commutes u v)

composition-preserves-commutability : {A B C : Set₁}
                                    → (f : A → A → B)
                                    → (g : B → C)
                                    → (comm-f :  ∀ x y
                                              →  f x y
                                              ≡₁ f y x)
                                    →  ∀ x y
                                    →  g (f x y)
                                    ≡₁ g (f y x)
composition-preserves-commutability f g comm-f x y = cong₁₁ g (comm-f x y)

&commutes : ∀ {A B}
          → (f : ⟦ & A ⟧ → ⟦ B ⟧)
          →  ∀ x y
          →  f (drop-order x y)
          ≡₁ f (drop-order y x)
&commutes f = composition-preserves-commutability drop-order f drop-order-commutes
