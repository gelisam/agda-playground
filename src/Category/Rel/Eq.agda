module Category.Rel.Eq where

open import Relation.Binary.PropositionalEquality

open import Category.SetC
open import Category.Rel
open import Functor
open import Adjunction


Eq : Functor Set# Rel#
Eq = record
   { tmap = λ A → record
          { A  = A
          ; A' = A
          ; A~ = _≡_
          }
   ; fmap = λ f ra
          → let open Val ra in record
          { a  = f
          ; a' = f
          ; a~ = cong f a~
          }
   }

eq-refl : ∀ {A}
        → A
        → Val (Eq ⋅ A)
eq-refl a = record
          { a  = a
          ; a' = a
          ; a~ = refl
          }

Contraction : Functor Rel# Set#
Contraction = record
            { tmap = λ R → Val R
            ; fmap = λ rf ra
                   → let open Val ra in
                     let open Val (rf ra) renaming
                            ( a  to f
                            ; a' to f'
                            ; a~ to f~
                            ) in record
                   { a  = f  a
                   ; a' = f' a'
                   ; a~ = f~
                   }
            }

Eq⊣Contraction : Adj Set# Rel#
Eq⊣Contraction = record
               { F   = Eq
               ; G   = Contraction
               ; F⊣G = λ rf a
                     → let open Val (rf (eq-refl a)) renaming
                              ( a  to f
                              ; a' to f'
                              ; a~ to f~
                              ) in record
                     { a  = f  a
                     ; a' = f' a
                     ; a~ = f~
                     }
               ; G⊢F = λ {A} {B} f ra
                     → let open Val ra in record
                     { a  = λ x  → Val.a  (f x )
                     ; a' = λ x' → Val.a' (f x')
                     ; a~ = subst (λ x' → Rel.A~ B
                                            (Val.a  (f a ))
                                            (Val.a' (f x')))
                                  a~
                                  (Val.a~ (f a))
                     }
               }
