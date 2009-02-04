module Syntactic where

-- This is based on a technique described by Nils Anders Danielsson.

-- The sort ■ classifies the kind ✯.  As ✯ is the only kind (for now),
-- we don't strictly need to mention it below, but it makes the rules
-- more uniform in my opinion.
data ■ : Set where
  ✯ : ■

-- Inductive-recursive definition of the object language (in this
-- case, a variant intuitionistic FOL).  Kinding and typing rules are
-- encoded directy in the syntax, therefore making it impossible to
-- write ill-kinded types (propositions) or ill-typed terms (proofs).
mutual

  -- Contexts
  infixl 1 _▹_
  data Ctx : Set where
    -- Empty
    ε   : Ctx

    -- Snoc
    _▹_ : (Γ : Ctx)
        → Γ ⊩ ✯
        → Ctx

  -- Simultaneous substitutions
  infix  0 _⇒_
  infix  3 _↑_
  infixr 3 _∘_
  data _⇒_ : Ctx → Ctx → Set where
    -- Create a substitution for a term
    subst  : ∀ {Γ τ}
           → Γ ⊢ τ
           → Γ ▹ τ ⇒ Γ

    weaken : ∀ {Γ} τ
           → Γ ⇒ Γ ▹ τ

    -- Lift a simultaneous substitution by one additional variable
    -- (i.e., extend with a new zero)
    _↑_    : ∀ {Γ Δ}
           → (ρ : Γ ⇒ Δ)
           → (τ : Γ ⊩ ✯)
           → Γ ▹ τ ⇒ Δ ▹ τ /⊩ ρ

    id     : ∀ {Γ}
           → Γ ⇒ Γ

    _∘_    : ∀ {Γ Δ X}
           → Γ ⇒ Δ
           → Δ ⇒ X
           → Γ ⇒ X

  -- Intrinsically-kinded types
  infix 0 _⊩_
  infix 3 _≡_
  data _⊩_ : Ctx → ■ → Set where
    ⊥   : ∀ {Γ}
        → Γ ⊩ ✯

    ⊤   : ∀ {Γ}
        → Γ ⊩ ✯

    Π   : ∀ {Γ}
        → (τ : Γ ⊩ ✯)
        → Γ ▹ τ ⊩ ✯
        → Γ ⊩ ✯

    -- Intensional equality predicate
    _≡_ : ∀ {Γ τ}
        → (t₁ : Γ ⊢ τ)
        → (t₂ : Γ ⊢ τ)
        → Γ ⊩ ✯

  infixr 1 _⊃_
  _⊃_ : ∀ {Γ}
      → Γ ⊩ ✯
      → Γ ⊩ ✯
      → Γ ⊩ ✯
  τ₁ ⊃ τ₂ = Π τ₁ (τ₂ /⊩ weaken τ₁)

  ¬_ : ∀ {Γ}
     → Γ ⊩ ✯
     → Γ ⊩ ✯
  ¬ τ = τ ⊃ ⊥

  -- Variables
  infix 0 _∋_
  data _∋_ : (Γ : Ctx) → Γ ⊩ ✯ → Set where
    vz : ∀ {Γ τ}
       → Γ ▹ τ ∋ τ /⊩ weaken τ

    vs : ∀ {Γ τ₁ τ₂}
       → Γ ∋ τ₁
       → Γ ▹ τ₂ ∋ τ₁ /⊩ weaken τ₂

  -- Intrinsically-typed terms with explicit simultaneous
  -- substitutions
  infix  0 _⊢_
  infix  4 _/⊢_
  infixr 0 ƛ_
  infixl 1 _·_
  data _⊢_ : (Γ : Ctx) → Γ ⊩ ✯ → Set where
    abort  : ∀ {Γ τ}
           → Γ ⊢ ⊥
           → Γ ⊢ τ

    tt     : ∀ {Γ}
           → Γ ⊢ ⊤

    var    : ∀ {Γ τ}
           → Γ ∋ τ
           → Γ ⊢ τ

    ƛ_     : ∀ {Γ τ₁ τ₂}
           → Γ ▹ τ₁ ⊢ τ₂
           → Γ ⊢ Π τ₁ τ₂

    _·_    : ∀ {Γ τ₁ τ₂}
           → Γ ⊢ Π τ₁ τ₂
           → (t₂ : Γ ⊢ τ₁)
           → Γ ⊢ τ₂ /⊩ subst t₂

    -- Evidence for the intensional equality predicate (_≡_)
    refl  : ∀ {Γ τ}
          → (t : Γ ⊢ τ)
          → Γ ⊢ t ≡ t

    -- Apply a simultaneous substitution to a term
    _/⊢_  : ∀ {Γ τ Δ}
          → Γ ⊢ τ
          → (ρ : Γ ⇒ Δ)
          → Δ ⊢ τ /⊩ ρ

  -- Apply a simultaneous substitution to a type
  infix 2 _/⊩_
  _/⊩_ : ∀ {Γ Δ}
       → Γ ⊩ ✯
       → Γ ⇒ Δ
       → Δ ⊩ ✯
  ⊥       /⊩ ρ = ⊥
  ⊤       /⊩ ρ = ⊤
  Π τ₁ τ₂ /⊩ ρ = Π (τ₁ /⊩ ρ) (τ₂ /⊩ ρ ↑ τ₁)
  t₁ ≡ t₂ /⊩ ρ = t₁ /⊢ ρ ≡ t₂ /⊢ ρ

-- Examples
tt≡tt : ∀ {Γ} → Γ ⊢ tt ≡ tt
tt≡tt = refl tt

-- The following should type check, but it takes too long and too much memory to run on my macbook...
-- λ ¬¬¬p → λ p → ¬¬¬p (λ ¬p → ¬p p)
-- ¬¬¬P⊃¬P : ∀ {Γ} (P : Γ ⊩ ✯) → Γ ⊢ ¬ ¬ ¬ P ⊃ ¬ P
-- ¬¬¬P⊃¬P P = ƛ ƛ var (vs vz) · (ƛ var vz · var (vs vz))

