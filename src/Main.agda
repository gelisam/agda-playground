module Main where

open import Data.Fin
open import Data.Nat


-- two recursive positions which both have access
-- to n variables
data App (n : ℕ)
       : ℕ
       → Set
         where
  AppFun
    : App n n
  AppArg
    : App n n

-- one recursive position which has access to 1+n
-- variables
data Lam (n : ℕ)
       : ℕ
       → Set
         where
  LamBody
    : Lam n (suc n)

data TermF : (ℕ → ℕ → Set)
           → Set
             where
  TermApp
    : TermF App
  TermLam
    : TermF Lam

data Freer (f : (ℕ → ℕ → Set) → Set)
           (a : ℕ → Set)
           (outer : ℕ)
         : Set₁
           where
  Pure : a outer
       → Freer f a outer
  Bind : ∀ {rel}
       → f rel
       → ( ∀ {inner}
         → rel outer inner
         → Freer f a inner
         )
       → Freer f a outer

two : Freer TermF Fin 0
two
  = Bind TermLam λ  -- s
    { LamBody →
        Bind TermLam λ  -- z
        { LamBody →
            Bind TermApp λ
            { AppFun →
                Pure (# 1)  -- s
            ; AppArg →
                Bind TermApp λ
                { AppFun →
                    Pure (# 1)  -- s
                ; AppArg →
                    Pure (# 0)  -- z
                }
            }
        }
    }
