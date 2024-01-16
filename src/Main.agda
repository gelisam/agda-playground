module Main where

open import Data.List using (List; []; _∷_; _++_; [_])
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

data Ty : Set where
  NatTy : Ty
  _:->:_ : Ty → Ty → Ty

infixr 4 _:->:_


-----------
-- Terms --
-----------

data Term (gamma : List Ty) : Ty → Set where
  Var
    : ∀ {ty}
    → Elem ty gamma
    → Term gamma ty
  NatLit
    : ℕ
    → Term gamma NatTy
  App
    : ∀ {ty1 ty2}
    → Term gamma (ty1 :->: ty2)
    → Term gamma ty1
    → Term gamma ty2
  Lam
    : ∀ {ty1 ty2}
    → Term (gamma ++ [ ty1 ]) ty2
    → Term gamma (ty1 :->: ty2)


---------------
-- Weakening --
---------------

module _ {A : Set} where
  data _⊆_ : List A → List A → Set where
    []
      : [] ⊆ []
    yes∷_
      : ∀ {x xs xys}
      → xs ⊆ xys
      → x ∷ xs ⊆ x ∷ xys
    no∷_
      : ∀ {y xs xys}
      → xs ⊆ xys
      → xs ⊆ y ∷ xys
  infix 4 _⊆_

  emptySubset
    : ∀ {xys : List A}
    → [] ⊆ xys
  emptySubset {[]}
    = []
  emptySubset {_ ∷ xys}
    = no∷ (emptySubset {xys})

  fullSubset
    : ∀ {xs : List A}
    → xs ⊆ xs
  fullSubset {[]}
    = []
  fullSubset {_ ∷ xs}
    = yes∷ (fullSubset {xs})

  _++[yes]
    : ∀ {x : A} {xs xys}
    → xs ⊆ xys
    → (xs ++ [ x ]) ⊆ (xys ++ [ x ])
  [] ++[yes]
    = yes∷ []
  (yes∷ subset) ++[yes]
    = yes∷ (subset ++[yes])
  (no∷ subset) ++[yes]
    = no∷ (subset ++[yes])

  _++[no]
    : ∀ {x : A} {xs xys}
    → xs ⊆ xys
    → xs ⊆ (xys ++ [ x ])
  [] ++[no]
    = no∷ []
  (yes∷ subset) ++[no]
    = yes∷ (subset ++[no])
  (no∷ subset) ++[no]
    = no∷ (subset ++[no])

  weakenElem
    : ∀ {x : A} {xs xys}
    → xs ⊆ xys
    → Elem x xs
    → Elem x xys
  weakenElem (yes∷_ _) Here
    = Here
  weakenElem (yes∷ xs) (There i)
    = There (weakenElem xs i)
  weakenElem (no∷ xs) i
    = There (weakenElem xs i)

weakenTerm
  : ∀ {gamma gamma' ty}
  → gamma ⊆ gamma'
  → Term gamma ty
  → Term gamma' ty
weakenTerm gammaSubset (Var i)
  = Var (weakenElem gammaSubset i)
weakenTerm _ (NatLit n)
  = NatLit n
weakenTerm gammaSubset (App ef e1)
  = App
      (weakenTerm gammaSubset ef)
      (weakenTerm gammaSubset e1)
weakenTerm gammaSubset (Lam e)
  = Lam (weakenTerm (gammaSubset ++[yes]) e)

closedTerm
  : ∀ {gamma ty}
  → Term [] ty
  → Term gamma ty
closedTerm
  = weakenTerm emptySubset


--------------
-- Examples --
--------------

foldℕ : ∀ {A : Set} → A → (A → A) → ℕ → A
foldℕ z _ zero
  = z
foldℕ z s (suc n)
  = s (foldℕ z s n)

two
  : ∀ {gamma ty}
  → Term gamma ((ty :->: ty) :->: ty :->: ty)
two
  = closedTerm
  $ Lam {-s-}
  $ Lam {-z-}
  $ foldℕ
      (Var {-z-} (There Here))
      (App (Var {-s-} Here))
      2


-----------------------------
-- Values and environments --
-----------------------------

mutual
  data Value : Ty → Set where
    nat
      : ℕ
      → Value NatTy
    closure
      : ∀ {gamma ty1 ty2}
      → Env gamma
      → Term (gamma ++ [ ty1 ]) ty2
      → Value (ty1 :->: ty2)

  data Env : List Ty → Set where
    []
      : Env []
    _∷_
      : ∀ {ty gamma}
      → Value ty
      → Env gamma
      → Env (ty ∷ gamma)


--------------------------------------
-- Value and environment operations --
--------------------------------------

lookup
  : ∀ {ty gamma}
  → Elem ty gamma
  → Env gamma
  → Value ty
lookup Here (v ∷ _)
  = v
lookup (There i) (_ ∷ vs)
  = lookup i vs

snocEnv
  : ∀ {gamma ty}
  → Env gamma
  → Value ty
  → Env (gamma ++ [ ty ])
snocEnv [] v
  = v ∷ []
snocEnv (v₀ ∷ vs) v
  = v₀ ∷ snocEnv vs v


----------------
-- Evaluation --
----------------

{-# NON_TERMINATING #-}
evalTerm
  : ∀ {gamma ty}
  → Env gamma
  → Term gamma ty
  → Value ty
evalTerm env (Var i)
  = lookup i env
evalTerm _ (NatLit n)
  = nat n
evalTerm env (App ef e1) with evalTerm env ef | evalTerm env e1
... | closure capturedEnv e2 | v1
  = evalTerm (snocEnv capturedEnv v1) e2
evalTerm env (Lam e)
  = closure env e