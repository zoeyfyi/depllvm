{-# OPTIONS --cubical #-}

module Graph.Relation.Subgraph.Base where

open import Cubical.Foundations.Prelude
open import Graph.Base

infix 10 _⊆_

_⊆_ : ∀ {ℓ} {A : Type ℓ} -> Graph A -> Graph A -> Type ℓ
x ⊆ y = x + y ≡ y