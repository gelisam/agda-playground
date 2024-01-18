{-# OPTIONS --sized-types #-}
module Prelude where

open import Codata.Sized.Delay using (Delay; bind)


_$_ : {A B : Set} → (A → B) → A → B
_$_ f x = f x
infixr -1 _$_

_>>=_ : ∀ {A B : Set} {i} → Delay A i → (A → Delay B i) → Delay B i
_>>=_ = bind