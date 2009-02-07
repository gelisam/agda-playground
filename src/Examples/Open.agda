{-# OPTIONS --sized-types #-}
module Examples.Open where
open import Size
open import Data.Bool
open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Vec
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

data NatMatch : {Γ : ℕ} -> Open-ℕ Γ -> Set where
  hole   : {Γ : ℕ}(x : Open-ℕ (suc Γ)){prf : x ≡ var {suc Γ} zero} ->
           NatMatch x
  zero   : {Γ : ℕ} -> NatMatch (zero {Γ})
  suc    : {Γ : ℕ}{var : Open-ℕ Γ} -> NatMatch var -> NatMatch (suc var)
  weaker : {Γ : ℕ}{var : Open-ℕ Γ} -> NatMatch var -> NatMatch (weaken var)

match-nat : {Γ : ℕ}(n : Open-ℕ Γ) -> NatMatch n
match-nat {suc Γ} (var zero) = hole {Γ} (var {suc Γ} zero) {refl}
match-nat (var (suc i)) = weaker (match-nat (var i))
match-nat zero = zero
match-nat (suc n) = suc (match-nat n)

is-var : Open-ℕ 1 -> Bool
is-var n with match-nat n
is-var ._ | hole x             = true
is-var ._ | zero               = false
is-var ._ | suc {var = n} _    = false
is-var ._ | weaker {var = n} _ = false

cnt-nat : {Γ : ℕ} -> Open-ℕ (suc Γ) -> ℕ
cnt-nat n with match-nat n
cnt-nat ._ | hole x             = 1
cnt-nat ._ | zero               = 0
cnt-nat ._ | suc {var = n} _    = cnt-nat n
cnt-nat ._ | weaker {var = n} _ = 0


data Open-Exp (Γ : ℕ) : {i : Size} -> Set where
  nat  : {i : Size} ->
    Open-ℕ Γ -> Open-Exp Γ {↑ i}
  add  : {i : Size} ->
    Open-Exp Γ {i} -> Open-Exp Γ {i} -> Open-Exp Γ {↑ i}
  letE : {i : Size} ->
    Open-Exp Γ {i} -> Open-Exp (suc Γ) {i} -> Open-Exp Γ {↑ i}

_exp[_] : {Γ1 Γ2 : ℕ}{i : Size} ->
  Open-Exp Γ1 {i} -> Vec (Open-ℕ Γ2) Γ1 -> Open-Exp Γ2 {i}
nat n exp[ sub ] = nat (n nat[ sub ])
add e1 e2 exp[ sub ] = add (e1 exp[ sub ]) (e2 exp[ sub ])
letE e1 e2 exp[ sub ] =
  letE
    (e1 exp[ sub ])
    (e2 exp[ var zero ∷ map weaken sub ])

data ExpMatch : {Γ : ℕ} -> Open-Exp Γ -> Set where
  nat    : {Γ : ℕ}{var : Open-ℕ Γ} ->
           NatMatch var -> ExpMatch (nat var)
  add    : {Γ : ℕ}{var1 var2 : Open-Exp Γ} ->
           ExpMatch var1 -> ExpMatch var2 -> ExpMatch (add var1 var2)
  letE   : {Γ : ℕ}{var1 : Open-Exp Γ}{var2 : Open-Exp (suc Γ)} ->
           ExpMatch var1 -> ExpMatch var2 -> ExpMatch (letE var1 var2)

match-exp : {Γ : ℕ}(e : Open-Exp Γ) -> ExpMatch e
match-exp (nat n) = nat (match-nat n)
match-exp (add  e1 e2) = add (match-exp e1) (match-exp e2)
match-exp (letE e1 e2) = letE (match-exp e1) (match-exp e2)

id-ψ : {Γ : ℕ} -> Vec (Open-ℕ Γ) Γ
id-ψ {zero}  = []
id-ψ {suc _} = var zero ∷ map weaken id-ψ

-- mutual
--   data HOAS-ℕ : (Γ : ℕ) -> Set where
--     hole : {Γ : ℕ} -> HOAS-ℕ (suc Γ)
--     λ    : {Γ : ℕ} -> (HOAS-ℕ (suc Γ) -> HOAS-ℕ (suc Γ)) ->
--                         HOAS-ℕ (suc Γ)
--     zero : {Γ : ℕ} -> HOAS-ℕ Γ
--     suc  : {Γ : ℕ} -> HOAS-ℕ Γ -> HOAS-ℕ Γ
--     _[_] : {Γ ψ : ℕ} -> Open-ℕ ψ -> Sub-ℕ Γ ψ -> HOAS-ℕ Γ
--   data Sub-ℕ (Γ : ℕ) : (ψ : ℕ) -> Set where
--     []   : Sub-ℕ Γ zero
--     _∷_ : {ψ : ℕ} -> HOAS-ℕ Γ -> Sub-ℕ Γ ψ -> Sub-ℕ Γ (suc ψ)
--     id-ψ : {ψ : ℕ} -> Sub-ℕ Γ ψ

-- box : {Γ : ℕ} (ℕ -> Open-Exp Γ) -> Open-Exp (suc Γ)

cnt-exp : {Γ : ℕ}{i : Size} -> Open-Exp (suc Γ) {i} -> ℕ
cnt-exp (nat n) = cnt-nat n
cnt-exp (add e1 e2) = cnt-exp e1 + cnt-exp e2
cnt-exp (letE e1 e2) =
  cnt-exp e1 +
  cnt-exp (e2 exp[
    var (suc zero) ∷
    var zero ∷
    map weaken (map weaken id-ψ)
  ])
