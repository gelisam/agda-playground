module Int where

-- module Seq where
--   infixr 0 _➝_
--   infixl 2 _×_
--   infixl 1 _+_
--   data Form : Set where
--     _➝_ : Form → Form → Form
--     _×_ : Form → Form → Form
--     _+_ : Form → Form → Form

--   infixl 1 _,_
--   data Ctx  : Set where
--     ε   : Ctx
--     _,_ : Ctx → Form → Ctx

--   infix 0 _∋_
--   data _∋_ : Ctx → Form → Set where
--     vz : ∀ {Γ X}
--       → Γ , X ∋ X

--     vs : ∀ {Γ X₁ X₂}
--       → Γ      ∋ X₂
--       → Γ , X₁ ∋ X₂

--   infix 0 _⊢_
--   data _⊢_ : Ctx → Form → Set where
--     id     : ∀ {Γ X}
--            → Γ ∋ X
--            → Γ ⊢ X

--     -- Left rules
--     ƛfold  : ∀ {Γ A B γ}
--            → Γ     ∋ A ➝ B
--            → Γ     ⊢ A
--            → Γ , B ⊢ γ
--            → Γ     ⊢ γ

--     ×fold  : ∀ {Γ A B γ}
--            → Γ         ∋ A × B
--            → Γ , A , B ⊢ γ
--            → Γ         ⊢ γ

--     +fold  : ∀ {Γ A B γ}
--            → Γ     ∋ A + B
--            → Γ , A ⊢ γ
--            → Γ , B ⊢ γ
--            → Γ     ⊢ γ

--     -- Right rules
--     ƛ_     : ∀ {Γ A B}
--            → Γ , A ⊢ B
--            → Γ     ⊢ A ➝ B

--     ⟨_,_⟩  : ∀ {Γ A B}
--            → Γ ⊢ A
--            → Γ ⊢ B
--            → Γ ⊢ A × B

--     inl    : ∀ {Γ A B}
--            → Γ ⊢ A
--            → Γ ⊢ A + B

--     inr    : ∀ {Γ A B}
--            → Γ ⊢ B
--            → Γ ⊢ A + B

module FocSeq where

  module Formulas where
    mutual
      data Pos : Set where
        ↓   : Neg → Pos
        0⁺  : Pos
        _+_ : Pos → Pos → Pos
        1⁺  : Pos
        _×_ : Pos → Pos → Pos

      data Neg : Set where
        ↑   : Pos → Neg
        ⊤⁻  : Neg
        _➝_ : Pos → Neg → Neg
        _&_ : Neg → Neg → Neg



  module Contexts where
    open Formulas public

    -- Linear Context
    infixr 1 _,_
    data LCtx : Set where
      ε   : LCtx
      _,_ : LCtx → Neg → LCtx

    infix 0 _∋_
    data _∋_ : LCtx → Neg → Set where
      vz : ∀ {Δ X}
         → Δ , X ∋ X

      vs : ∀ {Δ X₁ X₂}
         → Δ      ∋ X₂
         → Δ , X₁ ∋ X₂

    infixl 2 _++_
    _++_ : LCtx → LCtx → LCtx
    Δ₁ ++ ε        = Δ₁
    Δ₁ ++ (Δ₂ , x) = Δ₁ ++ Δ₂ , x 

    data L²Ctx : Set where
      ε   : L²Ctx
      _,_ : L²Ctx → LCtx → L²Ctx

    infix 0 _∋²_
    data _∋²_ : L²Ctx → LCtx → Set where
      vz : ∀ {Γ Δ}
         → Γ , Δ ∋² Δ

      vs : ∀ {Γ Δ₁ Δ₂}
         → Γ      ∋² Δ₂
         → Γ , Δ₁ ∋² Δ₂


  module Patterns where
    open Contexts public

    infix 0 _⇒⁺_
    data _⇒⁺_ : LCtx → Pos → Set where
      ⟨⟩    : ε ⇒⁺ 1⁺

      ⟨_,_⟩ : ∀ {Δ₁ Δ₂ A B}
            → Δ₁       ⇒⁺ A
            →       Δ₂ ⇒⁺     B
            → Δ₁ ++ Δ₂ ⇒⁺ A × B

      inl   : ∀ {Δ A B}
            → Δ ⇒⁺ A
            → Δ ⇒⁺ A + B

      inr   : ∀ {Δ A B}
            → Δ ⇒⁺     B
            → Δ ⇒⁺ A + B

    infix 0 _▸_⇒⁻_
    data _▸_⇒⁻_ : LCtx → Neg → Pos → Set where
      _·_ : ∀ {Δ₁ Δ₂ A⁺ B⁻ γ}
          → Δ₁                 ⇒⁺ A⁺
          → Δ₂       ▸      B⁻ ⇒⁻ γ
          → Δ₁ ++ Δ₂ ▸ A⁺ ➝ B⁻ ⇒⁻ γ

      π₁  : ∀ {Δ A⁻ B⁻ γ}
          → Δ ▸ A⁻      ⇒⁻ γ
          → Δ ▸ A⁻ & B⁻ ⇒⁻ γ

      π₂  : ∀ {Δ A⁻ B⁻ γ}
          → Δ ▸      B⁻ ⇒⁻ γ
          → Δ ▸ A⁻ & B⁻ ⇒⁻ γ



  module Logic where
    open Patterns public

    mutual
      infix 0 _⊢⁺[_]
      data _⊢⁺[_] : L²Ctx → Pos → Set where
        val⁺ : ∀ {Γ A⁺ Δ}
             → Δ ⇒⁺ A⁺
             → Γ ⇉ Δ
             → Γ ⊢⁺[ A⁺ ]

      infix 0 _▸_⊢⁺_
      data _▸_⊢⁺_ : L²Ctx → Pos → Pos → Set where
        con⁺ : ∀ {Γ A⁺ γ}
             → (∀ {Δ} → Δ ⇒⁺ A⁺ → Γ , Δ ⊢⁺ γ)
             → Γ ▸ A⁺ ⊢⁺ γ

      infix 0 _⊢⁻_
      data _⊢⁻_ : L²Ctx → Neg → Set where
        val⁻ : ∀ {Γ A⁻}
             → (∀ {Δ γ} → Δ ▸ A⁻ ⇒⁻ γ → Γ , Δ ⊢⁺ γ)
             → Γ ⊢⁻ A⁻

      infix 0 _▸[_]⊢⁻_
      data _▸[_]⊢⁻_ : L²Ctx → Neg → Pos → Set where
        con⁻ : ∀ {Δ A⁻ γ₁ γ₂ Γ}
             → Δ ▸ A⁻ ⇒⁻ γ₁
             → Γ ⇉ Δ
             → Γ ▸ γ₁ ⊢⁺ γ₂
             → Γ ▸[ A⁻ ]⊢⁻ γ₂

      infix 0 _⊢⁺_
      data _⊢⁺_ : L²Ctx → Pos → Set where
        ret : ∀ {Γ A⁺}
            → Γ ⊢⁺[ A⁺ ]
            → Γ ⊢⁺ A⁺

--         app : ∀ {Γ} {A⁻ γ}
--             → (Γ ∋² A⁻ → Γ ▸[ A⁻ ]⊢⁻ γ)
--             → Γ ⊢⁺ γ

      infix 0 _⇉_
      data _⇉_ : L²Ctx → LCtx → Set where