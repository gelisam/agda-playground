{-# OPTIONS --sized-types #-}
module Main where

open import Codata.Sized.Delay using (Delay; now; later; bind; runFor)
open import Codata.Sized.Thunk using (force)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Size using (Size)


--------------------
-- Standard stuff --
--------------------

_$_ : {A B : Set} → (A → B) → A → B
_$_ f x = f x
infixr -1 _$_

_>>=_ : ∀ {A B : Set} {i} → Delay A i → (A → Delay B i) → Delay B i
_>>=_ = bind

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

-- STLC is strongly-normalizing, but proving so is not the point of this
-- example, so we use Delay to allow the evaluator to diverge. Later, we
-- use runFor to evaluate the examples for a finite number of steps.

evalTerm
  : ∀ {gamma ty i}
  → Env gamma
  → Term gamma ty
  → Delay (Value ty) i
evalTerm env (Var i) = do
  now $ lookup i env
evalTerm _ Zero = do
  now (Nat 0)
evalTerm env (Succ e) = later λ where .force → do
  Nat n ← evalTerm env e
  now $ Nat $ suc n
evalTerm env (App ef e1) = later λ where .force → do
  Closure capturedEnv e2 ← evalTerm env ef
  v1 ← evalTerm env e1
  v2 ← evalTerm (snocEnv capturedEnv v1) e2
  now v2
evalTerm env (Lam e) = do
  now $ Closure env e


----------------------
-- Run the examples --
----------------------

evalZero : runFor 2 (evalTerm [] (Succ Zero))
         ≡ just (Nat 1)
evalZero = refl

evalTwo : runFor 7 (evalTerm [] (two · succ · Zero))
        ≡ just (Nat 2)
evalTwo = refl

evalFour : runFor 17 (evalTerm [] (four · succ · Zero))
         ≡ just (Nat 4)
evalFour = refl
