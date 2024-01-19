{-# OPTIONS --sized-types #-}
module Main where

open import Codata.Sized.Delay using (Delay; now; later; bind; runFor)
open import Codata.Sized.Thunk using (force)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Prelude

open import Elem
open import Subset

------------
-- Phases --
------------

-- The phase 1 code contains macro definitions.
-- The phase 0 code contains macro calls.
data Phase : Set where
  Phase1 : Phase
  Phase0 : Phase

-----------
-- Types --
-----------

data Ty : Phase → Set where
  NatTy
    : ∀ {phase}
    → Ty phase
  _:->:_
    : ∀ {phase}
    → Ty phase
    → Ty phase
    → Ty phase
  DiaTy
    : Ty Phase0
    → Ty Phase1

infixr 4 _:->:_


-----------
-- Terms --
-----------

-- * mu contains the phase 1 macro definitions.
-- * gamma contains the phase 0 variables.
data Term (mu : List (Ty Phase1)) (gamma : List (Ty Phase0)) : (phase : Phase) → Ty phase → Set where
  Var0
    : ∀ {ty}
    → Elem ty gamma
    → Term mu gamma Phase0 ty
  Var1
    : ∀ {ty}
    → Elem ty mu
    → Term mu gamma Phase1 ty
  Zero
    : ∀ {phase}
    → Term mu gamma phase NatTy
  Succ
    : ∀ {phase}
    → Term mu gamma phase NatTy
    → Term mu gamma phase NatTy
  FoldNat
    : ∀ {phase ty}
    → Term mu gamma phase ty
    → Term mu gamma phase (ty :->: ty)
    → Term mu gamma phase NatTy
    → Term mu gamma phase ty
  App
    : ∀ {phase ty1 ty2}
    → Term mu gamma phase (ty1 :->: ty2)
    → Term mu gamma phase ty1
    → Term mu gamma phase ty2
  Lam0
    : ∀ {ty1 ty2}
    → Term mu (gamma ++ [ ty1 ]) Phase0 ty2
    → Term mu gamma Phase0 (ty1 :->: ty2)
  Lam1
    : ∀ {ty1 ty2}
    → Term (mu ++ [ ty1 ]) gamma Phase1 ty2
    → Term mu gamma Phase1 (ty1 :->: ty2)
  Let0
    : ∀ {ty1 ty2}
    → Term mu gamma Phase0 ty1
    → Term mu (gamma ++ [ ty1 ]) Phase0 ty2
    → Term mu gamma Phase0 ty2
  Let1
    : ∀ {ty1 ty2}
    → Term mu gamma Phase1 ty1
    → Term (mu ++ [ ty1 ]) gamma Phase1 ty2
    → Term mu gamma Phase1 ty2
  LetMacro
    : ∀ {ty1 ty2}
    → Term mu gamma Phase1 ty1
    → Term (mu ++ [ ty1 ]) gamma Phase0 ty2
    → Term mu gamma Phase0 ty2
  MacroCall
    : ∀ {ty}
    → Term mu gamma Phase1 (DiaTy ty)
    → Term mu gamma Phase0 ty
  Quote
    : ∀ {ty}
    → Term mu gamma Phase0 ty
    → Term mu gamma Phase1 (DiaTy ty)
  LetQuote
    : ∀ {ty1 ty2}
    → Term mu gamma Phase1 (DiaTy ty1)
    → Term mu (gamma ++ [ ty1 ]) Phase1 ty2
    → Term mu gamma Phase1 ty2


---------------
-- Weakening --
---------------

weakenTerm
  : ∀ {mu mu' gamma gamma' phase ty}
  → mu ⊆ mu'
  → gamma ⊆ gamma'
  → Term mu gamma phase ty
  → Term mu' gamma' phase ty
weakenTerm _ gammaSubset (Var0 i)
  = Var0 (weakenElem gammaSubset i)
weakenTerm muSubset _ (Var1 i)
  = Var1 (weakenElem muSubset i)
weakenTerm _ _ Zero
  = Zero
weakenTerm muSubset gammaSubset (Succ e)
  = Succ
      (weakenTerm muSubset gammaSubset e)
weakenTerm muSubset gammaSubset (FoldNat ez es en)
  = FoldNat
      (weakenTerm muSubset gammaSubset ez)
      (weakenTerm muSubset gammaSubset es)
      (weakenTerm muSubset gammaSubset en)
weakenTerm muSubset gammaSubset (App ef e1)
  = App
      (weakenTerm muSubset gammaSubset ef)
      (weakenTerm muSubset gammaSubset e1)
weakenTerm muSubset gammaSubset (Lam0 e)
  = Lam0
      (weakenTerm muSubset (gammaSubset ++[yes]) e)
weakenTerm muSubset gammaSubset (Lam1 e)
  = Lam1
      (weakenTerm (muSubset ++[yes]) gammaSubset e)
weakenTerm muSubset gammaSubset (Let0 e1 e2)
  = Let0
      (weakenTerm muSubset gammaSubset e1)
      (weakenTerm muSubset (gammaSubset ++[yes]) e2)
weakenTerm muSubset gammaSubset (Let1 e1 e2)
  = Let1
      (weakenTerm muSubset gammaSubset e1)
      (weakenTerm (muSubset ++[yes]) gammaSubset e2)
weakenTerm muSubset gammaSubset (LetMacro e1 e2)
  = LetMacro
      (weakenTerm muSubset gammaSubset e1)
      (weakenTerm (muSubset ++[yes]) gammaSubset e2)
weakenTerm muSubset gammaSubset (MacroCall e)
  = MacroCall
      (weakenTerm muSubset gammaSubset e)
weakenTerm muSubset gammaSubset (Quote e)
  = Quote
      (weakenTerm muSubset gammaSubset e)
weakenTerm muSubset gammaSubset (LetQuote e1 e2)
  = LetQuote
      (weakenTerm muSubset gammaSubset e1)
      (weakenTerm muSubset (gammaSubset ++[yes]) e2)

closedTerm
  : ∀ {mu gamma phase ty}
  → Term [] [] phase ty
  → Term mu gamma phase ty
closedTerm
  = weakenTerm emptySubset emptySubset


--------------
-- Examples --
--------------

_·_
  : ∀ {mu gamma phase ty1 ty2}
  → Term mu gamma phase (ty1 :->: ty2)
  → Term mu gamma phase ty1
  → Term mu gamma phase ty2
_·_ = App
infixl 9 _·_

natLit
  : ∀ {mu gamma phase}
  → ℕ
  → Term mu gamma phase NatTy
natLit zero
  = Zero
natLit (suc n)
  = Succ (natLit n)

succ
  : ∀ {mu gamma}
  → Term mu gamma Phase0 (NatTy :->: NatTy)
succ
  = closedTerm
  $ Lam0 $ let x = Var0 Here
 in Succ x

add
  : ∀ {mu gamma}
  → Term mu gamma Phase0 (NatTy :->: NatTy :->: NatTy)
add
  = closedTerm
  $ Lam0 $ let x = Var0 Here
 in Lam0 $ let y = Var0 (There Here)
 in FoldNat y succ x

times
  : ∀ {mu gamma}
  → Term mu gamma Phase0 (NatTy :->: NatTy :->: NatTy)
times
  = closedTerm
  $ Lam0 $ let x = Var0 Here
 in Lam0 $ let y = Var0 (There Here)
 in FoldNat Zero (add · y) x

power
  : ∀ {mu gamma}
  → Term mu gamma Phase1 (NatTy :->: DiaTy NatTy :->: DiaTy NatTy)
power
  = closedTerm
  $ Lam1 $ let n = Var1 Here
 in Lam1 $ let diaX = Var1 (There Here)
 in LetQuote diaX $ let x = Var0 Here
 in FoldNat
      (Quote (natLit 1))
      ( Lam1 $ let diaX^⟨x-1⟩ = Var1 (There (There Here))
     in LetQuote diaX^⟨x-1⟩ $ let x^⟨x-1⟩ = Var0 (There Here)
     in Quote
      $ times · x^⟨x-1⟩ · x
      )
      n

square
  : ∀ {mu gamma}
  → Term mu gamma Phase0 (NatTy :->: NatTy)
square
  = closedTerm
  $ LetMacro power $ let power = Var1 Here
 in Lam0 $ let x = Var0 Here
 in MacroCall
  $ power · natLit 2 · Quote x


------------------
-- Substitution --
------------------

-- A simultaneous substitution: all the variables in sigma are replaced with a
-- Term in gamma. We only use this during macro expansion, not during
-- evaluation, so we don't need a separate type for replacing variables with
-- MacroTerms.

data Subst (gamma : List (Ty Phase0)) : List (Ty Phase0) → Set where
  []
    : Subst gamma []
  _∷_
    : ∀ {ty sigma}
    → Term [] gamma Phase0 ty
    → Subst gamma sigma
    → Subst gamma (ty ∷ sigma)

weakenSubst
  : ∀ {gamma gamma' sigma}
  → gamma ⊆ gamma'
  → Subst gamma sigma
  → Subst gamma' sigma
weakenSubst _ []
  = []
weakenSubst subset (e ∷ subst)
  = weakenTerm fullSubset subset e
  ∷ weakenSubst subset subst

idSubst
  : ∀ {gamma}
  → Subst gamma gamma
idSubst {[]}
  = []
idSubst {_ ∷ gamma}
  = Var0 Here
  ∷ weakenSubst (no∷ fullSubset) idSubst

-- Extend the substitution with a variable which gets replaced by itself.
_++[var]
  : ∀ {gamma sigma ty}
  → Subst gamma sigma
  → Subst (gamma ++ [ ty ]) (sigma ++ [ ty ])
[] ++[var]
  = Var0 lastElem ∷ []
(e ∷ subst) ++[var]
  = weakenTerm fullSubset (fullSubset ++[no]) e
  ∷ subst ++[var]

snocSubst
  : ∀ {gamma sigma ty}
  → Subst gamma sigma
  → Term [] gamma Phase0 ty
  → Subst gamma (sigma ++ [ ty ])
snocSubst [] e
  = e ∷ []
snocSubst (e₀ ∷ subst) e
  = e₀ ∷ snocSubst subst e

substVar
  : ∀ {gamma sigma ty}
  → Subst gamma sigma
  → Elem ty sigma
  → Term [] gamma Phase0 ty
substVar (e ∷ _) Here
  = e
substVar (_ ∷ sigma) (There i)
  = substVar sigma i

substTerm
  : ∀ {mu gamma sigma phase ty}
  → Subst gamma sigma
  → Term mu sigma phase ty
  → Term mu gamma phase ty
substTerm subst (Var0 i)
  = weakenTerm emptySubset fullSubset
  $ substVar subst i
substTerm subst (Var1 i)
  = Var1 i
substTerm _ Zero
  = Zero
substTerm subst (Succ e)
  = Succ (substTerm subst e)
substTerm subst (FoldNat ez es en)
  = FoldNat
      (substTerm subst ez)
      (substTerm subst es)
      (substTerm subst en)
substTerm subst (App ef e1)
  = App
      (substTerm subst ef)
      (substTerm subst e1)
substTerm {mu} {gamma} {sigma} subst (Lam0 {ty1} e)
  = Lam0 (substTerm subst' e)
  where
    subst' : Subst (gamma ++ [ ty1 ]) (sigma ++ [ ty1 ])
    subst' = subst ++[var]
substTerm subst (Lam1 e)
  = Lam1 (substTerm subst e)
substTerm {mu} {gamma} {sigma} subst (Let0 {ty1} e1 e2)
  = Let0
      (substTerm subst e1)
      (substTerm subst' e2)
  where
    subst' : Subst (gamma ++ [ ty1 ]) (sigma ++ [ ty1 ])
    subst' = subst ++[var]
substTerm subst (Let1 e1 e2)
  = Let1
      (substTerm subst e1)
      (substTerm subst e2)
substTerm subst (LetMacro e1 e2)
  = LetMacro
      (substTerm subst e1)
      (substTerm subst e2)
substTerm subst (MacroCall e)
  = MacroCall (substTerm subst e)
substTerm subst (Quote e)
  = Quote (substTerm subst e)
substTerm {mu} {gamma} {sigma} subst (LetQuote {ty1} e1 e2)
  = LetQuote
      (substTerm subst e1)
      (substTerm subst' e2)
  where
    subst' : Subst (gamma ++ [ ty1 ]) (sigma ++ [ ty1 ])
    subst' = subst ++[var]


-----------------------------
-- Values and environments --
-----------------------------

mutual
  data Value : Ty Phase0 → Set where
    Nat
      : ℕ
      → Value NatTy
    Closure
      : ∀ {gamma ty1 ty2}
      → Env gamma
      → Term [] (gamma ++ [ ty1 ]) Phase0 ty2
      → Value (ty1 :->: ty2)

  data Env : List (Ty Phase0) → Set where
    []
      : Env []
    _∷_
      : ∀ {ty gamma}
      → Value ty
      → Env gamma
      → Env (ty ∷ gamma)

mutual
  data MacroValue (gamma : List (Ty Phase0)) : Ty Phase1 → Set where
    Nat
      : ℕ
      → MacroValue gamma NatTy
    Closure
      : ∀ {mu ty1 ty2}
      → MacroEnv mu gamma
      → Term (mu ++ [ ty1 ]) gamma Phase1 ty2
      → MacroValue gamma (ty1 :->: ty2)
    QuotedTerm
      : ∀ {ty}
      → Term [] gamma Phase0 ty
      → MacroValue gamma (DiaTy ty)

  data MacroEnv : List (Ty Phase1) → List (Ty Phase0) → Set where
    []
      : ∀ {gamma}
      → MacroEnv [] gamma
    _∷_
      : ∀ {mu gamma ty}
      → MacroValue gamma ty
      → MacroEnv mu gamma
      → MacroEnv (ty ∷ mu) gamma


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

lookupMacro
  : ∀ {ty mu gamma}
  → Elem ty mu
  → MacroEnv mu gamma
  → MacroValue gamma ty
lookupMacro Here (v ∷ _)
  = v
lookupMacro (There i) (_ ∷ vs)
  = lookupMacro i vs

snocEnv
  : ∀ {gamma ty}
  → Env gamma
  → Value ty
  → Env (gamma ++ [ ty ])
snocEnv [] v
  = v ∷ []
snocEnv (v₀ ∷ vs) v
  = v₀ ∷ snocEnv vs v

snocMacroEnv
  : ∀ {mu gamma ty}
  → MacroEnv mu gamma
  → MacroValue gamma ty
  → MacroEnv (mu ++ [ ty ]) gamma
snocMacroEnv [] v
  = v ∷ []
snocMacroEnv (v₀ ∷ vs) v
  = v₀ ∷ snocMacroEnv vs v

mutual
  weakenMacroValue
    : ∀ {gamma gamma' ty}
    → gamma ⊆ gamma'
    → MacroValue gamma ty
    → MacroValue gamma' ty
  weakenMacroValue _ (Nat n)
    = Nat n
  weakenMacroValue subset (Closure env e)
    = Closure
        (weakenMacroEnv subset env)
        (weakenTerm fullSubset subset e)
  weakenMacroValue subset (QuotedTerm e)
    = QuotedTerm (weakenTerm fullSubset subset e)

  weakenMacroEnv
    : ∀ {mu gamma gamma'}
    → gamma ⊆ gamma'
    → MacroEnv mu gamma
    → MacroEnv mu gamma'
  weakenMacroEnv _ []
    = []
  weakenMacroEnv subset (v ∷ vs)
    = weakenMacroValue subset v
    ∷ weakenMacroEnv subset vs


---------------------
-- Macro expansion --
---------------------

-- expand evaluates all the MacroTerms contained inside a Term, while keeping
-- the Term portions intact. LetQuote-bound variables and MacroCall invocations
-- are replaced with the calculated Terms.
--
-- I don't know if this calculus is strongly-normalizing, so I use Delay to
-- allow the expander and evaluator to diverge. Later, I use runFor to expand
-- and evaluate the examples for a finite number of steps.

mutual
  expand
    : ∀ {mu gamma ty i}
    → MacroEnv mu gamma
    → Term mu gamma Phase0 ty
    → Delay (Term [] gamma Phase0 ty) i
  expand _ (Var0 i) = do
    now $ Var0 i
  expand _ Zero = do
    now Zero
  expand env (Succ e) = later λ where .force → do
    e' ← expand env e
    now $ Succ e'
  expand env (FoldNat ez es en) = later λ where .force → do
    ez' ← expand env ez
    es' ← expand env es
    en' ← expand env en
    now $ FoldNat ez' es' en'
  expand env (App ef e1) = later λ where .force → do
    ef' ← expand env ef
    e1' ← expand env e1
    now $ App ef' e1'
  expand {mu} {gamma} env (Lam0 {ty1} e) = do
    let env' : MacroEnv mu (gamma ++ [ ty1 ])
        env' = weakenMacroEnv (fullSubset ++[no]) env
    e' ← expand env' e
    now $ Lam0 e'
  expand {mu} {gamma} env (Let0 {ty1} e1 e2) = do
    e1' ← expand env e1
    let env' : MacroEnv mu (gamma ++ [ ty1 ])
        env' = weakenMacroEnv (fullSubset ++[no]) env
    e2' ← expand env' e2
    now $ Let0 e1' e2'
  expand {mu} {gamma} env (LetMacro {ty1} e1 e2) = later λ where .force → do
    v1 ← evalMacroTerm env e1
    let env' : MacroEnv (mu ++ [ ty1 ]) gamma
        env' = snocMacroEnv env v1
    e2' ← expand env' e2
    now e2'
  expand env (MacroCall e) = later λ where .force → do
    QuotedTerm e' ← evalMacroTerm env e
    now e'

  evalMacroTerm
    : ∀ {mu gamma ty i}
    → MacroEnv mu gamma
    → Term mu gamma Phase1 ty
    → Delay (MacroValue gamma ty) i
  evalMacroTerm env (Var1 i) = do
    now $ lookupMacro i env
  evalMacroTerm _ Zero = do
    now $ Nat zero
  evalMacroTerm env (Succ e) = later λ where .force → do
    Nat n ← evalMacroTerm env e
    now $ Nat $ suc n
  evalMacroTerm {mu} {gamma} {ty} {i} env (FoldNat ez es en) = later λ where .force → do
    Nat n ← evalMacroTerm env en
    evalMacroTerm env
      ( Let1 ez
      $ Let1 (weakenTerm (fullSubset ++[no]) fullSubset es)
      $ weakenTerm (emptySubset ++[yes] ++[yes]) emptySubset
      $ go n
      )
    where
      z : Term (ty ∷ (ty :->: ty) ∷ []) [] Phase1 ty
      z = Var1 Here

      s : Term (ty ∷ (ty :->: ty) ∷ []) [] Phase1 (ty :->: ty)
      s = Var1 (There Here)

      go : ℕ → Term (ty ∷ (ty :->: ty) ∷ []) [] Phase1 ty
      go zero
        = z
      go (suc n)
        = App s (go n)
  evalMacroTerm env (App ef e1) = later λ where .force → do
    Closure capturedEnv e2 ← evalMacroTerm env ef
    v1 ← evalMacroTerm env e1
    v2 ← evalMacroTerm (snocMacroEnv capturedEnv v1) e2
    now v2
  evalMacroTerm env (Lam1 e) = do
    now $ Closure env e
  evalMacroTerm env (Let1 e1 e2) = later λ where .force → do
    v1 ← evalMacroTerm env e1
    v2 ← evalMacroTerm (snocMacroEnv env v1) e2
    now v2
  evalMacroTerm env (Quote e) = later λ where .force → do
    e' ← expand env e
    now $ QuotedTerm e'
  evalMacroTerm {mu} {gamma} env (LetQuote {ty1} {ty2} e1 e2) = later λ where .force → do
    -- It's a bit strange to use a substitution in the middle of an
    -- environment-based evaluator, but I tried a few alternatives and this
    -- seems to be the most straightforward way to do it.
    QuotedTerm e1' ← evalMacroTerm env e1
    let subst : Subst gamma (gamma ++ [ ty1 ])
        subst = snocSubst idSubst e1'
    let e2 : Term mu gamma Phase1 ty2
        e2 = substTerm subst e2
    evalMacroTerm env e2



-------------------------
-- Expand the examples --
-------------------------

expandSquare : runFor 40 (expand {[]} {[]} [] square)
             ≡ just ( Lam0 $ let x = Var0 Here
                   in times · (times · natLit 1 · x) · x
                    )
expandSquare = refl
