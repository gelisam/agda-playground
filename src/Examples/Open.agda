{-# OPTIONS --sized-types #-}
module Examples.Open where
open import Size
open import Data.Bool
open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Vec hiding (map)
open import Data.Vec1 hiding (lookup)
open import Data.HList
open import Data.Product1
open import Data.Fun.Type
open import Data.Pat
open import Data.Pat.Helper
open import Data.Pat.Cover
open import Data.Pat.Case
open import Relation.Binary.PropositionalEquality


data Open-ℕ (Γ : ℕ) : Set where
  var  : Fin Γ -> Open-ℕ Γ
  zero : Open-ℕ Γ
  suc  : Open-ℕ Γ -> Open-ℕ Γ

erase : Open-ℕ zero -> ℕ
erase (var ())
erase zero = zero
erase (suc n) = suc (erase n)

_nat[_] : {Γ1 Γ2 : ℕ} -> Open-ℕ Γ1 -> Vec (Open-ℕ Γ2) Γ1 -> Open-ℕ Γ2
var i nat[ sub ] = lookup i sub
zero nat[ sub ] = zero
suc n nat[ sub ] = suc (n nat[ sub ])

weaken : {Γ : ℕ} -> Open-ℕ Γ -> Open-ℕ (suc Γ)
weaken (var i) = var (suc i)
weaken zero = zero
weaken (suc n) = suc (weaken n)

-- view n : Open-ℕ[] of
--   box(. zero) ⇒ ...
--   box(. suc U[.]) ⇒ ...
view-z-s : View (Open-ℕ 0) 2
view-z-s = zero ∶ Open-ℕ 0 $
         ∷ suc  ∶ Open-ℕ 0 ⇾ Open-ℕ 0 $
         ∷ []

cover-z-s : Cover view-z-s
cover-z-s (var ())
cover-z-s zero    = cover-with view-z-s (# 0)
cover-z-s (suc x) = cover-with view-z-s (# 1) x

-- view n : Open-ℕ[Γ,x] of
--   box(φ,x. x) ⇒ ...
--   box(φ,x. zero) ⇒ ...
--   box(φ,x. suc U[id,x]) ⇒ ...
--   box(φ,x. U[id]) ⇒ ...
-- weak-var : {Γ : ℕ} → Open-ℕ (suc Γ)
-- weak-var {zero} = var 0
-- weak-var {suc n} = weaken weak-var
view-x-z-s-w : {Γ : ℕ} → View (Open-ℕ (suc Γ)) 4
view-x-z-s-w {Γ} = var zero ∶ Open-ℕ (suc Γ) $
                 ∷ zero     ∶ Open-ℕ (suc Γ) $
                 ∷ suc      ∶ Open-ℕ (suc Γ) ⇾ Open-ℕ (suc Γ) $
                 ∷ weaken   ∶ Open-ℕ      Γ  ⇾ Open-ℕ (suc Γ) $
                 ∷ []

cover-x-z-s-w : {Γ : ℕ} → Cover (view-x-z-s-w {Γ})
cover-x-z-s-w (var zero)    = cover-with view-x-z-s-w (# 0)
cover-x-z-s-w zero          = cover-with view-x-z-s-w (# 1)
cover-x-z-s-w (suc x)       = cover-with view-x-z-s-w (# 2) x
cover-x-z-s-w (var (suc n)) = cover-with view-x-z-s-w (# 3) (var n)

is-var : Open-ℕ 1 -> Bool
is-var n = case n cover-x-z-s-w
             true
             false
             (λ n → false)
             (λ n → false)

is-var2 : Open-ℕ 1 -> Bool
is-var2 n with cover-x-z-s-w n
is-var2 .(var zero) | (zero                       ,     []) , refl = true
is-var2 .zero       | (suc zero                   ,     []) , refl = false
is-var2 .(suc n)    | (suc (suc zero)             , n ∷ []) , refl = false
is-var2 .(weaken n) | (suc (suc (suc zero))       , n ∷ []) , refl = false
is-var2 _           | (suc (suc (suc (suc ())))   , _     ) , _

-- cnt-nat : {Γ : ℕ} -> Open-ℕ (suc Γ) -> ℕ
-- cnt-nat n = case n cover-x-z-s-w
--               1
--               0
--               (λ n → cnt-nat n)
--               (λ n → 0)


-- data Open-Exp (Γ : ℕ) : {i : Size} -> Set where
--   nat  : {i : Size} ->
--     Open-ℕ Γ -> Open-Exp Γ {↑ i}
--   add  : {i : Size} ->
--     Open-Exp Γ {i} -> Open-Exp Γ {i} -> Open-Exp Γ {↑ i}
--   letE : {i : Size} ->
--     Open-Exp Γ {i} -> Open-Exp (suc Γ) {i} -> Open-Exp Γ {↑ i}
-- 
-- _exp[_] : {Γ1 Γ2 : ℕ}{i : Size} ->
--   Open-Exp Γ1 {i} -> Vec (Open-ℕ Γ2) Γ1 -> Open-Exp Γ2 {i}
-- nat n exp[ sub ] = nat (n nat[ sub ])
-- add e1 e2 exp[ sub ] = add (e1 exp[ sub ]) (e2 exp[ sub ])
-- letE e1 e2 exp[ sub ] =
--   letE
--     (e1 exp[ sub ])
--     (e2 exp[ var zero ∷ map weaken sub ])
-- 
-- data ExpMatch : {Γ : ℕ} -> Open-Exp Γ -> Set where
--   nat    : {Γ : ℕ}{var : Open-ℕ Γ} ->
--            NatMatch var -> ExpMatch (nat var)
--   add    : {Γ : ℕ}{var1 var2 : Open-Exp Γ} ->
--            ExpMatch var1 -> ExpMatch var2 -> ExpMatch (add var1 var2)
--   letE   : {Γ : ℕ}{var1 : Open-Exp Γ}{var2 : Open-Exp (suc Γ)} ->
--            ExpMatch var1 -> ExpMatch var2 -> ExpMatch (letE var1 var2)
-- 
-- match-exp : {Γ : ℕ}(e : Open-Exp Γ) -> ExpMatch e
-- match-exp (nat n) = nat (match-nat n)
-- match-exp (add  e1 e2) = add (match-exp e1) (match-exp e2)
-- match-exp (letE e1 e2) = letE (match-exp e1) (match-exp e2)
-- 
-- id-ψ : {Γ : ℕ} -> Vec (Open-ℕ Γ) Γ
-- id-ψ {zero}  = []
-- id-ψ {suc _} = var zero ∷ map weaken id-ψ
-- 
-- -- mutual
-- --   data HOAS-ℕ : (Γ : ℕ) -> Set where
-- --     hole : {Γ : ℕ} -> HOAS-ℕ (suc Γ)
-- --     λ    : {Γ : ℕ} -> (HOAS-ℕ (suc Γ) -> HOAS-ℕ (suc Γ)) ->
-- --                         HOAS-ℕ (suc Γ)
-- --     zero : {Γ : ℕ} -> HOAS-ℕ Γ
-- --     suc  : {Γ : ℕ} -> HOAS-ℕ Γ -> HOAS-ℕ Γ
-- --     _[_] : {Γ ψ : ℕ} -> Open-ℕ ψ -> Sub-ℕ Γ ψ -> HOAS-ℕ Γ
-- --   data Sub-ℕ (Γ : ℕ) : (ψ : ℕ) -> Set where
-- --     []   : Sub-ℕ Γ zero
-- --     _∷_ : {ψ : ℕ} -> HOAS-ℕ Γ -> Sub-ℕ Γ ψ -> Sub-ℕ Γ (suc ψ)
-- --     id-ψ : {ψ : ℕ} -> Sub-ℕ Γ ψ
-- 
-- -- box : {Γ : ℕ} (ℕ -> Open-Exp Γ) -> Open-Exp (suc Γ)
-- 
-- cnt-exp : {Γ : ℕ}{i : Size} -> Open-Exp (suc Γ) {i} -> ℕ
-- cnt-exp (nat n) = cnt-nat n
-- cnt-exp (add e1 e2) = cnt-exp e1 + cnt-exp e2
-- cnt-exp (letE e1 e2) =
--   cnt-exp e1 +
--   cnt-exp (e2 exp[
--     var (suc zero) ∷
--     var zero ∷
--     map weaken (map weaken id-ψ)
--   ])
