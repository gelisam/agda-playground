module Semantic where

open import Data.Nat
open import Data.Function
open import Data.Product
open import Data.Unit

-- The following code is based on a technique described by Conor
-- McBride on the Agda mailing list.  The trick is to represent types
-- "semantically" rather than "syntactically".  This solves the
-- problem of having to reason about substitutions or equality in the
-- object language because these things are taken care of by the
-- metalanguage.

-- Things to explore:
-- 1.  How easy is it to work with this encoding?
-- 2.  How far does it scale? Clearly it works for the dependently
--     typed language below, which already implies it would work for
--     most practical programming languages.  Does it work for the
--     calculus of constructions?  Probably not since the CoC is not a
--     subset of Agda.
-- 3.  How easy is it to "clean up" the presentation (by using
--     well-named type aliases, etc.)?
-- 4.  Normalization is handled by evaluation into Agda.  How easy is
--     it to quote Agda values back into this language?  This would
--     give a normalizer that would go through Agda, but still give us
--     results in the object language, which would be desirable for
--     most metatheoretic results.  Because we are mapping into Set
--     during evaluation (from El), that means we will need to map
--     back out of Set during quotation afterward.  The only way I
--     think this can be possible is if we also have a proof that
--     whatever we evaluated and mapped into Set actually came from
--     something in this language.  This restricts the domain from Set
--     (which is too large -- there's plenty in Set that doesn't map
--     to this language for instance) to something small enough that
--     we can deal with.
-- 5.  There seem to be problems with unsolved metavariables in some
--     cases, for example: (λ x. s x) · z
--     Why is this?

mutual
  data ✯ : Set where
    true : ✯
    pi   : (τ : ✯) → (El τ → ✯) → ✯

  El : ✯ → Set
  El true       = ⊤
  El (pi τ₁ τ₂) = (x : El τ₁) → El (τ₂ x)

infixr 0 _⊃_
_⊃_ : ✯ → ✯ → ✯
τ₁ ⊃ τ₂ = pi τ₁ (const τ₂)

mutual
  infixl 1 _◂_
  data Ctx : Set where
    ε   : Ctx
    _◂_ : (Γ : Ctx) → (Env Γ → ✯) → Ctx

  Env : Ctx → Set
  Env ε       = ⊤
  Env (Γ ◂ E) = Σ (Env Γ) λ g → El (E g)

infix 0 _∋_
data _∋_ : (Γ : Ctx) → (Env Γ → ✯) → Set where
  vz : ∀ {Γ : Ctx} {τ : Env Γ → ✯}
     → Γ ◂ τ ∋ λ gτ → τ (proj₁ gτ)

  vs : ∀ {Γ : Ctx} {τ₁ τ₂ : Env Γ → ✯}
     → Γ ∋ τ₁
     → Γ ◂ τ₂ ∋ λ gτ₂ → τ₁ (proj₁ gτ₂)

ν : ∀ {Γ τ}
  → Γ ∋ τ
  → (E : Env Γ)
  → El (τ E)
ν vz     gτ = proj₂ gτ
ν (vs x) gτ = ν x (proj₁ gτ)

mutual
  infix 0 _⊩_
  data _⊩_ (Γ : Ctx) : (Env Γ → ✯) → Set where
    True : Γ ⊩ const true

    Pi   : ∀ {τ₁ τ₂}
         → Γ ⊩ τ₁
         → Γ ◂ τ₁ ⊩ τ₂
         → Γ ⊩ λ g → pi (τ₁ g) λ s → τ₂ (g , s)

  infix 0 _⊢_
  data _⊢_ (Γ : Ctx) : (τ : Env Γ → ✯) → Set where
    ⟨⟩  : Γ ⊢ const true

    var : ∀ {τ : Env Γ → ✯}
        → Γ ∋ τ
        → Γ ⊢ τ

    ƛ   : ∀ {τ₁ : Env Γ → ✯} {τ₂ : (g : Env Γ) → El (τ₁ g) → ✯}
        → Γ ⊩ τ₁
        → Γ ◂ τ₁ ⊢ (λ gt1 → τ₂ (proj₁ gt1) (proj₂ gt1))
        → Γ ⊢ λ g → pi (τ₁ g) (τ₂ g)

    _·_ : ∀ {τ₁ : Env Γ → ✯} {τ₂ : (g : Env Γ) (t1 : El (τ₁ g)) → ✯}
        → Γ ⊢ (λ g → (pi (τ₁ g) λ t1 → τ₂ g t1))
        → (t1 : Γ ⊢ τ₁)
        → Γ ⊢ λ g → τ₂ g (⟦ t1 ⟧ g)

  ⟦_⟧_ : ∀ {Γ τ}
       → Γ ⊢ τ
       → (E : Env Γ)
       → El (τ E)
  ⟦ ⟨⟩      ⟧ E = tt
  ⟦ var x   ⟧ E = ν x E
  ⟦ ƛ τ t₂  ⟧ E = λ t₁ → ⟦ t₂ ⟧ (E , t₁)
  ⟦ t₁ · t₂ ⟧ E = (⟦ t₁ ⟧ E) (⟦ t₂ ⟧ E)
