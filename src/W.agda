module W where

open import Data.Empty
open import Data.Unit

-- W types, the Well-ordering type constructor for Martin-Löf type
-- theory.  W types are capable of representing inductive data types
-- in a generic way.  M types are their coinductive duals.

-- The intuition is that α represents the "set of constructor labels"
-- for the type and ⟦_⟧ reoresents the decoder for the labels into
-- concrete sets in the universe.
data W (α : Set) (⟦_⟧ : α → Set) : Set where
  sup : (a : α) (f : ⟦ a ⟧ → W α ⟦_⟧) → W α ⟦_⟧

-- elimination of a W type (i.e., fold)
wrec : ∀ {α ⟦_⟧} {γ : W α ⟦_⟧ → Set}
     → (a : W α ⟦_⟧)
     → ((y : α) → (z : ⟦ y ⟧ → W α ⟦_⟧) → (u : (x : ⟦ y ⟧) → γ (z x)) → γ (sup y z))
     → γ a
wrec {γ = γ} (sup d e) b = b d e (λ x → wrec {γ = γ} (e x) b)

-- Example, Binary Trees as an instance of a W-type
module BinTree where
  open import Data.Nat

  -- First, we make a "label" type for the constructors we will want
  -- to use.
  data Tag : Set where
    Leaf : Tag
    Node : Tag

  -- For the Node constructor, we will need more "labels" specifying
  -- the positions available in the constructor.  Note, we could reuse
  -- these (or the tags) on other data types, to "pick and choose".
  -- That's the beauty of W-types.
  data Dir : Set where
    Left  : Dir
    Right : Dir

  -- We need a function to decode our constructor labels into concrete
  -- types in the universe.
  ⟦_⟧ : Tag → Set
  ⟦ Leaf ⟧ = ⊥
  ⟦ Node ⟧ = Dir

  -- Now we can make BinTree an alias for the W type of its labels and
  -- decoders.
  BinTree : Set
  BinTree = W Tag ⟦_⟧

  -- leaf is just one constructor for the BinTree (notice the absurd argument)
  leaf : BinTree
  leaf = sup Leaf λ()

  -- node is another
  node : BinTree → BinTree → BinTree
  node l r = sup Node dir 
    where
      dir : Dir → BinTree
      dir Left  = l
      dir Right = r

  -- an example tree
  example = node (node leaf (node leaf leaf)) leaf

  -- a function to count the number of notes (returns ? for example)
  numberOfNodes : BinTree → ℕ
  numberOfNodes x = wrec {γ = λ _ → ℕ} x f
    where
      f : (y : Tag) → (⟦ y ⟧ → BinTree) → (⟦ y ⟧ → ℕ) → ℕ
      f Leaf z u = 1
      f Node z u = u Left + u Right

-- another example
module Nat where
  open import Data.Function

  data Tag : Set where
    Zero : Tag
    Succ : Tag

  ⟦_⟧ : Tag → Set
  ⟦ Zero ⟧ = ⊥
  ⟦ Succ ⟧ = ⊤

  Nat : Set
  Nat = W Tag ⟦_⟧

  zero : Nat
  zero = sup Zero λ()

  succ : Nat → Nat
  succ n = sup Succ (const n)

  -- using natrec, what is add, mul, and exp?
  natrec : Nat → Nat → (Nat → Nat → Nat) → Nat
  natrec a b c = wrec {γ = λ _ → Nat} a f
    where
      f : (y : Tag) → (⟦ y ⟧ → Nat) → (⟦ y ⟧ → Nat) → Nat
      f Zero z u = b
      f Succ z u = c (z tt) (u tt)

module List (α : Set) where
  open import Data.Function
  open import Data.Sum

  List : Set
  List = W (⊤ ⊎ α) ⟦_⟧ where
    ⟦_⟧ : ⊤ ⊎ α → Set
    ⟦ inj₁ tt ⟧ = ⊥
    ⟦ inj₂ α  ⟧ = ⊤

  ε : List
  ε = sup (inj₁ tt) λ()

  infixr 5 _∷_
  _∷_ : α → List → List
  _∷_ x xs = sup (inj₂ x) (const xs)

module Vector (α : Set) where
  open import Data.Function
  open import Data.Product
  open import Data.Nat

  Vector : ℕ → Set
  Vector zero = W ⊤ ⟦_⟧ where
    ⟦_⟧ : ⊤ → Set
    ⟦ tt ⟧ = ⊥
  Vector (suc n) = W (α × Vector n) ⟦_⟧ where
    ⟦_⟧ : (α × Vector n) → Set
    ⟦ x , xs ⟧ = ⊥

  ε : Vector zero
  ε = sup tt λ()

  infixr 5 _∷_
  _∷_ : ∀ {n} → α → Vector n → Vector (suc n)
  _∷_ x xs = sup (x , xs) λ()
