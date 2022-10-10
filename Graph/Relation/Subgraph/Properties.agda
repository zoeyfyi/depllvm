{-# OPTIONS --cubical #-}

module Graph.Relation.Subgraph.Properties where

open import Cubical.Foundations.Prelude
open import Graph.Base
open import Graph.Properties
open import Graph.Relation.Subgraph.Base

private
  variable
    ℓ : Level
    A : Type ℓ
    x y z : Graph A

⊆-refl : x ⊆ x
⊆-refl = +-idemp

