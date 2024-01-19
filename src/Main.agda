{-# OPTIONS --sized-types #-}
module Main where

open import Codata.Sized.Delay using (Delay; now; later; bind; runFor)
open import Codata.Sized.Thunk using (force)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; zero; suc)

open import Prelude

open import Elem
open import Subset


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


---------------
-- Weakening --
---------------

mutual
  weakenTerm
    : ∀ {mu mu' gamma gamma' ty}
    → mu ⊆ mu'
    → gamma ⊆ gamma'
    → Term mu gamma ty
    → Term mu' gamma' ty
  weakenTerm _ gammaSubset (Var i)
    = Var (weakenElem gammaSubset i)
  weakenTerm _ _ Zero
    = Zero
  weakenTerm muSubset gammaSubset (Succ e)
    = Succ (weakenTerm muSubset gammaSubset e)
  weakenTerm muSubset gammaSubset (FoldNat ez es en)
    = FoldNat
        (weakenTerm muSubset gammaSubset ez)
        (weakenTerm muSubset gammaSubset es)
        (weakenTerm muSubset gammaSubset en)
  weakenTerm muSubset gammaSubset (App ef e1)
    = App
        (weakenTerm muSubset gammaSubset ef)
        (weakenTerm muSubset gammaSubset e1)
  weakenTerm muSubset gammaSubset (Lam e)
    = Lam (weakenTerm muSubset (gammaSubset ++[yes]) e)
  weakenTerm muSubset gammaSubset (Let e1 e2)
    = Let
        (weakenTerm muSubset gammaSubset e1)
        (weakenTerm muSubset (gammaSubset ++[yes]) e2)
  weakenTerm muSubset gammaSubset (LetMacro e1 e2)
    = LetMacro
        (weakenMacroTerm muSubset gammaSubset e1)
        (weakenTerm (muSubset ++[yes]) gammaSubset e2)
  weakenTerm muSubset gammaSubset (MacroCall e)
    = MacroCall (weakenMacroTerm muSubset gammaSubset e)

  weakenMacroTerm
    : ∀ {mu mu' gamma gamma' ty}
    → mu ⊆ mu'
    → gamma ⊆ gamma'
    → MacroTerm mu gamma ty
    → MacroTerm mu' gamma' ty
  weakenMacroTerm muSubset _ (Var i)
    = Var (weakenElem muSubset i)
  weakenMacroTerm _ _ Zero
    = Zero
  weakenMacroTerm muSubset gammaSubset (Succ e)
    = Succ (weakenMacroTerm muSubset gammaSubset e)
  weakenMacroTerm muSubset gammaSubset (FoldNat ez es en)
    = FoldNat
        (weakenMacroTerm muSubset gammaSubset ez)
        (weakenMacroTerm muSubset gammaSubset es)
        (weakenMacroTerm muSubset gammaSubset en)
  weakenMacroTerm muSubset gammaSubset (App ef e1)
    = App
        (weakenMacroTerm muSubset gammaSubset ef)
        (weakenMacroTerm muSubset gammaSubset e1)
  weakenMacroTerm muSubset gammaSubset (Lam e)
    = Lam (weakenMacroTerm (muSubset ++[yes]) gammaSubset e)
  weakenMacroTerm muSubset gammaSubset (Let e1 e2)
    = Let
        (weakenMacroTerm muSubset gammaSubset e1)
        (weakenMacroTerm (muSubset ++[yes]) gammaSubset e2)
  weakenMacroTerm muSubset gammaSubset (Quote e)
    = Quote (weakenTerm muSubset gammaSubset e)
  weakenMacroTerm muSubset gammaSubset (LetQuote e1 e2)
    = LetQuote
        (weakenMacroTerm muSubset gammaSubset e1)
        (weakenMacroTerm muSubset (gammaSubset ++[yes]) e2)

closedTerm
  : ∀ {mu gamma ty}
  → Term [] [] ty
  → Term mu gamma ty
closedTerm
  = weakenTerm emptySubset emptySubset

closedMacroTerm
  : ∀ {mu gamma ty}
  → MacroTerm [] [] ty
  → MacroTerm mu gamma ty
closedMacroTerm
  = weakenMacroTerm emptySubset emptySubset


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

add
  : ∀ {mu gamma}
  → Term mu gamma (NatTy :->: NatTy :->: NatTy)
add
  = closedTerm
  $ Lam $ let x = Var Here
 in Lam $ let y = Var (There Here)
 in FoldNat
      y
      ( Lam $ let x-1+y = Var (There (There Here))
     in Succ x-1+y
      )
      x

macroAdd
  : ∀ {mu gamma}
  → MacroTerm mu gamma (NatTy :->: NatTy :->: NatTy)
macroAdd
  = closedMacroTerm
  $ Lam $ let x = Var Here
 in Lam $ let y = Var (There Here)
 in FoldNat
      y
      ( Lam $ let x-1+y = Var (There (There Here))
     in Succ x-1+y
      )
      x

times
  : ∀ {mu gamma}
  → Term mu gamma (NatTy :->: NatTy :->: NatTy)
times
  = closedTerm
  $ Lam $ let x = Var Here
 in Lam $ let y = Var (There Here)
 in FoldNat
      Zero
      ( Lam $ let ⟨x-1⟩*y = Var (There (There Here))
     in App (App add ⟨x-1⟩*y) y
      )
      x

macroTimes
  : ∀ {mu gamma}
  → MacroTerm mu gamma (NatTy :->: NatTy :->: NatTy)
macroTimes
  = closedMacroTerm
  $ Lam $ let x = Var Here
 in Lam $ let y = Var (There Here)
 in FoldNat
      Zero
      ( Lam $ let ⟨x-1⟩*y = Var (There (There Here))
      in App (App macroAdd ⟨x-1⟩*y) y
      )
      x

power : MacroTerm [] [] (NatTy :->: DiaTy NatTy :->: DiaTy NatTy)
power
  = Lam $ let n = Var Here
 in Lam $ let diaX = Var (There Here)
 in LetQuote diaX $ let x = Var Here
 in FoldNat
      (Quote (natLit 1))
      ( Lam $ let diaX^⟨x-1⟩ = Var (There (There Here))
     in LetQuote diaX^⟨x-1⟩ $ let x^⟨x-1⟩ = Var (There Here)
     in Quote
      $ App (App times x^⟨x-1⟩) x
      )
      n

square : Term [] [] (NatTy :->: NatTy)
square
  = LetMacro power $ let power = Var Here
 in Lam $ let x = Var Here
 in MacroCall
  $ App (App power (macroNatLit 2)) (Quote x)


------------------
-- Substitution --
------------------

-- A simultaneous substitution: all the variables in sigma are replaced with a
-- Term in gamma. We only use this during macro expansion, not during
-- evaluation, so we don't need a separate type for replacing variables with
-- MacroTerms.

data Subst (gamma : List Ty) : List Ty → Set where
  []
    : Subst gamma []
  _∷_
    : ∀ {ty sigma}
    → Term [] gamma ty
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
  = Var Here
  ∷ weakenSubst (no∷ fullSubset) idSubst

-- Extend the substitution with a variable which gets replaced by itself.
_++[var]
  : ∀ {gamma sigma ty}
  → Subst gamma sigma
  → Subst (gamma ++ [ ty ]) (sigma ++ [ ty ])
[] ++[var]
  = Var lastElem ∷ []
(e ∷ subst) ++[var]
  = weakenTerm fullSubset (fullSubset ++[no]) e
  ∷ subst ++[var]

snocSubst
  : ∀ {gamma sigma ty}
  → Subst gamma sigma
  → Term [] gamma ty
  → Subst gamma (sigma ++ [ ty ])
snocSubst [] e
  = e ∷ []
snocSubst (e₀ ∷ subst) e
  = e₀ ∷ snocSubst subst e

substVar
  : ∀ {gamma sigma ty}
  → Subst gamma sigma
  → Elem ty sigma
  → Term [] gamma ty
substVar (e ∷ _) Here
  = e
substVar (_ ∷ sigma) (There i)
  = substVar sigma i

mutual
  substTerm
    : ∀ {mu gamma sigma ty}
    → Subst gamma sigma
    → Term mu sigma ty
    → Term mu gamma ty
  substTerm subst (Var i)
    = weakenTerm emptySubset fullSubset
    $ substVar subst i
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
  substTerm {mu} {gamma} {sigma} subst (Lam {ty1} e)
    = Lam (substTerm subst' e)
    where
      subst' : Subst (gamma ++ [ ty1 ]) (sigma ++ [ ty1 ])
      subst' = subst ++[var]
  substTerm {mu} {gamma} {sigma} subst (Let {ty1} e1 e2)
    = Let
        (substTerm subst e1)
        (substTerm subst' e2)
    where
      subst' : Subst (gamma ++ [ ty1 ]) (sigma ++ [ ty1 ])
      subst' = subst ++[var]
  substTerm {mu} {gamma} {sigma} subst (LetMacro {ty1} e1 e2)
    = LetMacro
        (substMacroTerm subst e1)
        (substTerm subst e2)
  substTerm subst (MacroCall e)
    = MacroCall (substMacroTerm subst e)

  substMacroTerm
    : ∀ {mu gamma sigma ty}
    → Subst gamma sigma
    → MacroTerm mu sigma ty
    → MacroTerm mu gamma ty
  substMacroTerm _ (Var i)
    = Var i
  substMacroTerm _ Zero
    = Zero
  substMacroTerm subst (Succ e)
    = Succ (substMacroTerm subst e)
  substMacroTerm subst (FoldNat ez es en)
    = FoldNat
        (substMacroTerm subst ez)
        (substMacroTerm subst es)
        (substMacroTerm subst en)
  substMacroTerm subst (App ef e1)
    = App
        (substMacroTerm subst ef)
        (substMacroTerm subst e1)
  substMacroTerm subst (Lam e)
    = Lam (substMacroTerm subst e)
  substMacroTerm subst (Let e1 e2)
    = Let
        (substMacroTerm subst e1)
        (substMacroTerm subst e2)
  substMacroTerm subst (Quote e)
    = Quote (substTerm subst e)
  substMacroTerm {mu} {gamma} {sigma} subst (LetQuote {ty1} e1 e2)
    = LetQuote
        (substMacroTerm subst e1)
        (substMacroTerm subst' e2)
    where
      subst' : Subst (gamma ++ [ ty1 ]) (sigma ++ [ ty1 ])
      subst' = subst ++[var]


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
      → Term [] (gamma ++ [ ty1 ]) ty2
      → Value (ty1 :->: ty2)

  data Env : List Ty → Set where
    []
      : Env []
    _∷_
      : ∀ {ty gamma}
      → Value ty
      → Env gamma
      → Env (ty ∷ gamma)

mutual
  data MacroValue (gamma : List Ty) : MacroTy → Set where
    Nat
      : ℕ
      → MacroValue gamma NatTy
    Closure
      : ∀ {mu ty1 ty2}
      → MacroEnv mu gamma
      → MacroTerm (mu ++ [ ty1 ]) gamma ty2
      → MacroValue gamma (ty1 :->: ty2)
    QuotedTerm
      : ∀ {ty}
      → Term [] gamma ty
      → MacroValue gamma (DiaTy ty)

  data MacroEnv : List MacroTy → List Ty → Set where
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
        (weakenMacroTerm fullSubset subset e)
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
    → Term mu gamma ty
    → Delay (Term [] gamma ty) i
  expand _ (Var i) = do
    now $ Var i
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
  expand {mu} {gamma} env (Lam {ty1} e) = do
    let env' : MacroEnv mu (gamma ++ [ ty1 ])
        env' = weakenMacroEnv (fullSubset ++[no]) env
    e' ← expand env' e
    now $ Lam e'
  expand {mu} {gamma} env (Let {ty1} e1 e2) = do
    e1' ← expand env e1
    let env' : MacroEnv mu (gamma ++ [ ty1 ])
        env' = weakenMacroEnv (fullSubset ++[no]) env
    e2' ← expand env' e2
    now $ Let e1' e2'
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
    → MacroTerm mu gamma ty
    → Delay (MacroValue gamma ty) i
  evalMacroTerm env (Var i) = do
    now $ lookupMacro i env
  evalMacroTerm _ Zero = do
    now $ Nat zero
  evalMacroTerm env (Succ e) = later λ where .force → do
    Nat n ← evalMacroTerm env e
    now $ Nat $ suc n
  evalMacroTerm {mu} {gamma} {ty} {i} env (FoldNat ez es en) = later λ where .force → do
    Nat n ← evalMacroTerm env en
    evalMacroTerm env
      ( Let ez
      $ Let (weakenMacroTerm (fullSubset ++[no]) fullSubset es)
      $ weakenMacroTerm (emptySubset ++[yes] ++[yes]) emptySubset
      $ go n
      )
    where
      z : MacroTerm (ty ∷ (ty :->: ty) ∷ []) [] ty
      z = Var Here

      s : MacroTerm (ty ∷ (ty :->: ty) ∷ []) [] (ty :->: ty)
      s = Var (There Here)

      go : ℕ → MacroTerm (ty ∷ (ty :->: ty) ∷ []) [] ty
      go zero
        = z
      go (suc n)
        = App s (go n)
  evalMacroTerm env (App ef e1) = later λ where .force → do
    Closure capturedEnv e2 ← evalMacroTerm env ef
    v1 ← evalMacroTerm env e1
    v2 ← evalMacroTerm (snocMacroEnv capturedEnv v1) e2
    now v2
  evalMacroTerm env (Lam e) = do
    now $ Closure env e
  evalMacroTerm env (Let e1 e2) = later λ where .force → do
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
    let e2 : MacroTerm mu gamma ty2
        e2 = substMacroTerm subst e2
    evalMacroTerm env e2
