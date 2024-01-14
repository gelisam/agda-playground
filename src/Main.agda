module Main where

open import Data.List
open import Data.Nat using (ℕ)


--------------------
-- Standard stuff --
--------------------

_$_ : {A B : Set} → (A → B) → A → B
_$_ f x = f x
infixr -1 _$_

data Elem {A : Set} : A → List A → Set where
  Here : ∀ {x xs} → Elem x (x ∷ xs)
  There : ∀ {x y xs} → Elem x xs → Elem x (y ∷ xs)


-----------
-- Types --
-----------

-- Types for the phase 0 code, including user-written code and code generated by
-- the macros.
data Ty : Set where
  NatTy : Ty
  _:->:_ : Ty → Ty → Ty

-- Types for the implementation of a macro. In this simplified setting, macro
-- definitions cannot themselves contain macro calls.
data MacroTy : Set where
  NatTy : MacroTy
  _:->:_ : MacroTy → MacroTy → MacroTy
  DiaTy : Ty → MacroTy

infixr 4 _:->:_


-----------
-- Terms --
-----------

mutual
  data MacroTerm (mu : List MacroTy) (gamma : List Ty) : MacroTy → Set where
    Var
      : ∀ {ty}
      → Elem ty mu
      → MacroTerm mu gamma ty
    NatLit
      : ℕ
      → MacroTerm mu gamma NatTy
    Add
      : MacroTerm mu gamma NatTy
      → MacroTerm mu gamma NatTy
      → MacroTerm mu gamma NatTy
    App
      : ∀ {ty1 ty2}
      → MacroTerm mu gamma (ty1 :->: ty2)
      → MacroTerm mu gamma ty1
      → MacroTerm mu gamma ty2
    Lam
      : ∀ {ty1 ty2}
      → MacroTerm (mu ++ [ ty1 ]) gamma ty2
      → MacroTerm mu gamma (ty1 :->: ty2)
    Let
      : ∀ {ty1 ty2}
      → MacroTerm mu gamma ty1
      → MacroTerm (mu ++ [ ty1 ]) gamma ty2
      → MacroTerm mu gamma ty2
    Quote
      : ∀ {ty}
      → Term mu gamma ty
      → MacroTerm mu gamma (DiaTy ty)
    LetQuote
      : ∀ {ty1 ty2}
      → MacroTerm mu gamma (DiaTy ty1)
      → MacroTerm mu (gamma ++ [ ty1 ]) ty2
      → MacroTerm mu gamma ty2

  -- * mu contains the phase 1 macro definitions.
  -- * gamma contains the phase 0 variables.
  data Term (mu : List MacroTy) (gamma : List Ty) : Ty → Set where
    Var
      : ∀ {ty}
      → Elem ty gamma
      → Term mu gamma ty
    NatLit
      : ℕ
      → Term mu gamma NatTy
    Add
      : Term mu gamma NatTy
      → Term mu gamma NatTy
      → Term mu gamma NatTy
    App
      : ∀ {ty1 ty2}
      → Term mu gamma (ty1 :->: ty2)
      → Term mu gamma ty1
      → Term mu gamma ty2
    Lam
      : ∀ {ty1 ty2}
      → Term mu (gamma ++ [ ty1 ]) ty2
      → Term mu gamma (ty1 :->: ty2)
    Let
      : ∀ {ty1 ty2}
      → Term mu gamma ty1
      → Term mu (gamma ++ [ ty1 ]) ty2
      → Term mu gamma ty2
    LetMacro
      : ∀ {ty1 ty2}
      → MacroTerm mu gamma ty1
      → Term (mu ++ [ ty1 ]) gamma ty2
      → Term mu gamma ty2
    MacroCall
      : ∀ {ty}
      → MacroTerm mu gamma (DiaTy ty)
      → Term mu gamma ty


--------------
-- Examples --
--------------

-- TODO: add recursion and pattern-matching in order to implement the macro for
-- real
power : MacroTerm [] [] (NatTy :->: DiaTy NatTy :->: DiaTy NatTy)
power
  = Lam {-n-}
  $ Lam {-x-}
  $ Var {-x-} (There Here)

square : Term [] [] (NatTy :->: NatTy)
square
  = LetMacro {-power-} {[]} {[]} {NatTy :->: DiaTy NatTy :->: DiaTy NatTy} power
  $ Lam {-x-}
  $ MacroCall
  $ App
      (App
        (Var {-power-} Here)
        (NatLit 2))
      (Quote (Var {-x-} Here))