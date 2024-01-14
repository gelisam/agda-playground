module Main where

open import Data.List
open import Data.Nat using (ℕ; zero; suc)


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
  -- * mu contains the phase 1 macro definitions.
  -- * gamma contains the phase 0 variables.
  data Term (mu : List MacroTy) (gamma : List Ty) : Ty → Set where
    Var
      : ∀ {ty}
      → Elem ty gamma
      → Term mu gamma ty
    Zero
      : Term mu gamma NatTy
    Succ
      : Term mu gamma NatTy
      → Term mu gamma NatTy
    FoldNat
      : ∀ {ty}
      → Term mu gamma ty
      → Term mu gamma (ty :->: ty)
      → Term mu gamma NatTy
      → Term mu gamma ty
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

  data MacroTerm (mu : List MacroTy) (gamma : List Ty) : MacroTy → Set where
    Var
      : ∀ {ty}
      → Elem ty mu
      → MacroTerm mu gamma ty
    Zero
      : MacroTerm mu gamma NatTy
    Succ
      : MacroTerm mu gamma NatTy
      → MacroTerm mu gamma NatTy
    FoldNat
      : ∀ {ty}
      → MacroTerm mu gamma ty
      → MacroTerm mu gamma (ty :->: ty)
      → MacroTerm mu gamma NatTy
      → MacroTerm mu gamma ty
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


--------------
-- Examples --
--------------

natLit
  : ∀ {mu gamma}
  → ℕ
  → Term mu gamma NatTy
natLit zero
  = Zero
natLit (suc n)
  = Succ (natLit n)

macroNatLit
  : ∀ {mu gamma}
  → ℕ
  → MacroTerm mu gamma NatTy
macroNatLit zero
  = Zero
macroNatLit (suc n)
  = Succ (macroNatLit n)

add'
  : Term [] [] (NatTy :->: NatTy :->: NatTy)
add'
  = Lam {-x-}
  $ Lam {-y-}
  $ FoldNat
      (Var {-y-} (There Here))
      ( Lam {- x-1 + y -}
      $ Succ (Var {- x-1 + y -} (There (There Here)))
      )
      (Var {-x-} Here)

-- TODO: weaken add' so it works in any context
add
  : ∀ {mu gamma}
  → Term mu gamma (NatTy :->: NatTy :->: NatTy)
add = _

macroAdd'
  : MacroTerm [] [] (NatTy :->: NatTy :->: NatTy)
macroAdd'
  = Lam {-x-}
  $ Lam {-y-}
  $ FoldNat
      (Var {-y-} (There Here))
      ( Lam {- x-1 + y -}
      $ Succ (Var {- x-1 + y -} (There (There Here)))
      )
      (Var {-x-} Here)

macroAdd
  : ∀ {mu gamma}
  → MacroTerm mu gamma (NatTy :->: NatTy :->: NatTy)
macroAdd = _

times'
  : Term [] [] (NatTy :->: NatTy :->: NatTy)
times'
  = Lam {-x-}
  $ Lam {-y-}
  $ FoldNat
      Zero
      ( Lam {- (x-1) * y -}
      $ App
          (App
            add
            (Var {- (x-1) * y -} (There (There Here))))
          (Var {-y-} (There Here))
      )
      (Var {-x-} Here)

times
  : ∀ {mu gamma}
  → Term mu gamma (NatTy :->: NatTy :->: NatTy)
times = _

macroTimes'
  : MacroTerm [] [] (NatTy :->: NatTy :->: NatTy)
macroTimes'
  = Lam {-x-}
  $ Lam {-y-}
  $ FoldNat
      Zero
      ( Lam {- (x-1) * y -}
      $ App
          (App
            macroAdd
            (Var {- (x-1) * y -} (There (There Here))))
          (Var {-y-} (There Here))
      )
      (Var {-x-} Here)

macroTimes
  : ∀ {mu gamma}
  → MacroTerm mu gamma (NatTy :->: NatTy :->: NatTy)
macroTimes = _

power : MacroTerm [] [] (NatTy :->: DiaTy NatTy :->: DiaTy NatTy)
power
  = Lam {-n-}
  $ Lam {-diaX-}
  $ LetQuote {-x-} (Var {-diaX-} (There Here))
  $ FoldNat
      (Quote (natLit 1))
      ( Lam {- power (n-1) diaX -}
      $ LetQuote {- power (n-1) x -} (Var {- power (n-1) diaX -} (There (There Here)))
      $ Quote
      $ App
          (App
            times
            (Var {- power (n-1) x -} (There Here)))
          (Var {-x-} Here)
      )
      (Var {-n-} Here)

square : Term [] [] (NatTy :->: NatTy)
square
  = LetMacro {-power-} power
  $ Lam {-x-}
  $ MacroCall
  $ App
      (App
        (Var {-power-} Here)
        (macroNatLit 2))
      (Quote (Var {-x-} Here))