-- A simplified version of Pfenning and Davies's modal type theory model of
-- staged computation.
--
-- The main simplification is that there are only two phases, so the quoted
-- terms (called 'InnerTerm' in this file) cannot themselves talk about quoted
-- terms.
--
-- The other simplification is that 'LetBox' only brings variables into scope
-- inside boxes, and thus cannot be used to evaluate quoted terms.
module PfenningDavies where

open import Data.List
open import Data.Nat using (ℕ)

_$_ : {A B : Set} → (A → B) → A → B
_$_ f x = f x
infixr -1 _$_

data Elem {A : Set} : A → List A → Set where
  Here : ∀ {x xs} → Elem x (x ∷ xs)
  There : ∀ {x y xs} → Elem x xs → Elem x (y ∷ xs)


data InnerTy : Set where
  NatTy : InnerTy
  _:->:_ : InnerTy → InnerTy → InnerTy

data OuterTy : Set where
  NatTy : OuterTy
  _:->:_ : OuterTy → OuterTy → OuterTy
  BoxTy : InnerTy → OuterTy

-- delta contains both the variables bound by LetBox and
-- the variables bound by InnerTerm.Lam and InnerTerm.Let
data InnerTerm (delta : List InnerTy) : InnerTy → Set where
  Var
    : ∀ {ty}
    → Elem ty delta
    → InnerTerm delta ty
  NatLit
    : ℕ
    → InnerTerm delta NatTy
  Add
    : InnerTerm delta NatTy
    → InnerTerm delta NatTy
    → InnerTerm delta NatTy
  App
    : ∀ {ty1 ty2}
    → InnerTerm delta (ty1 :->: ty2)
    → InnerTerm delta ty1
    → InnerTerm delta ty2
  Lam
    : ∀ {ty1 ty2}
    → InnerTerm (delta ++ [ ty1 ]) ty2
    → InnerTerm delta (ty1 :->: ty2)
  Let
    : ∀ {ty1 ty2}
    → InnerTerm delta ty1
    → InnerTerm (delta ++ [ ty1 ]) ty2
    → InnerTerm delta ty2

-- * delta contains the variables bound by LetBox
-- * gamma contains those bound by OuterTerm.Lam and OuterTerm.Let
data OuterTerm (delta : List InnerTy) (gamma : List OuterTy) : OuterTy → Set where
  Var
    : ∀ {ty}
    → Elem ty gamma
    → OuterTerm delta gamma ty
  NatLit
    : ℕ
    → OuterTerm delta gamma NatTy
  Add
    : OuterTerm delta gamma NatTy
    → OuterTerm delta gamma NatTy
    → OuterTerm delta gamma NatTy
  App
    : ∀ {ty1 ty2}
    → OuterTerm delta gamma (ty1 :->: ty2)
    → OuterTerm delta gamma ty1
    → OuterTerm delta gamma ty2
  Lam
    : ∀ {ty1 ty2}
    → OuterTerm delta (gamma ++ [ ty1 ]) ty2
    → OuterTerm delta gamma (ty1 :->: ty2)
  Box
    : ∀ {ty}
    → InnerTerm delta ty
    → OuterTerm delta gamma (BoxTy ty)
  Let
    : ∀ {ty1 ty2}
    → OuterTerm delta gamma ty1
    → OuterTerm delta (gamma ++ [ ty1 ]) ty2
    → OuterTerm delta gamma ty2
  LetBox
    : ∀ {ty1 ty2}
    → OuterTerm delta gamma (BoxTy ty1)
    → OuterTerm (delta ++ [ ty1 ]) gamma ty2
    → OuterTerm delta gamma ty2

mkLet1
  : OuterTerm [] [] (BoxTy NatTy)
  → OuterTerm [ NatTy ] [] (BoxTy (NatTy :->: NatTy))
  → OuterTerm [] [] (BoxTy NatTy)
mkLet1 boxedE1 boxedE2
  = LetBox {-e1-} boxedE1
  $ LetBox {-e2-} boxedE2
  $ Box
  $ Let (Var {-e1-} Here)
  $ App (Var {-e2-} (There Here))
        (Var {-x-} (There (There Here)))

boxedFortyThree1 : OuterTerm [] [] (BoxTy NatTy)
boxedFortyThree1
  = mkLet1
      (Box (NatLit 42))
      ( Box
      $ Lam {-y-}
      $ Add (Var {-y-} Here)
            (NatLit 1)
      )
