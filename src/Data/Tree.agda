module Data.Tree where

data Tree (α : Set) : Set where
  Branch : Tree α → α → Tree α → Tree α
  Leaf   : Tree α
