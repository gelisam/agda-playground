-- Example, Binary Trees as an instance of a W-type
module W.BinTree where
open import Data.Nat
open import Data.Empty
open import Data.Unit
open import Data.Function
open import W

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
