module Context where


infixr 6 _→t_
data Type : Set where
  unit : Type
  _→t_ : (τ₁ τ₂ : Type) → Type 

infixl 5 _▸_
data Context : Set where
  ε   : Context
  _▸_ : Context → Type → Context
