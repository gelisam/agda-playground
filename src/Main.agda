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
  Zero
    : Term gamma NatTy
  Succ
    : Term gamma NatTy
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
weakenTerm subset (Var i)
  = Var (weakenElem subset i)
weakenTerm _ Zero
  = Zero
weakenTerm subset (Succ e)
  = Succ (weakenTerm subset e)
weakenTerm subset (App ef e1)
  = App
      (weakenTerm subset ef)
      (weakenTerm subset e1)
weakenTerm subset (Lam e)
  = Lam (weakenTerm (subset ++[yes]) e)

closedTerm
  : ∀ {gamma ty}
  → Term [] ty
  → Term gamma ty
closedTerm
  = weakenTerm emptySubset


--------------
-- Examples --
--------------

_·_
  : ∀ {gamma ty1 ty2}
  → Term gamma (ty1 :->: ty2)
  → Term gamma ty1
  → Term gamma ty2
_·_ = App
infixl 9 _·_

succ
  : ∀ {gamma}
  → Term gamma (NatTy :->: NatTy)
succ
  = closedTerm
  $ Lam $ let x = Var Here
 in Succ x

two
  : ∀ {gamma ty}
  → Term gamma ((ty :->: ty) :->: ty :->: ty)
two
  = closedTerm
  $ Lam $ let s = Var Here
 in Lam $ let z = Var (There Here)
 in s · (s · z)

add
  : ∀ {gamma ty}
  → Term gamma
      ( ((ty :->: ty) :->: (ty :->: ty))
   :->: ((ty :->: ty) :->: (ty :->: ty))
   :->: ((ty :->: ty) :->: (ty :->: ty))
      )
add
  = closedTerm
  $ Lam $ let x = Var Here
 in Lam $ let y = Var (There Here)
 in Lam $ let s = Var (There (There Here))
 in Lam $ let z = Var (There (There (There Here)))
 in x · s · (y · s · z)

four
  : ∀ {gamma ty}
  → Term gamma ((ty :->: ty) :->: ty :->: ty)
four
  = closedTerm
  $ add · two · two


-----------------------------
-- Values and environments --
-----------------------------

mutual
  data Value : Ty → Set where
    Nat
      : ℕ
      → Value NatTy
    Closure
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
evalTerm _ Zero
  = Nat 0
evalTerm env (Succ e) with evalTerm env e
... | Nat n
  = Nat (suc n)
evalTerm env (App ef e1) with evalTerm env ef | evalTerm env e1
... | Closure capturedEnv e2 | v1
  = evalTerm (snocEnv capturedEnv v1) e2
evalTerm env (Lam e)
  = Closure env e