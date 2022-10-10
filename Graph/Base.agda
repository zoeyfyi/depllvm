-- Based on: https://github.com/algebraic-graphs/agda
{-# OPTIONS --cubical #-}

module Graph.Base where

open import Cubical.Foundations.Prelude

infixl 8  _+_
infixl 9  _⇒_

data Graph {ℓ} (A : Type ℓ) : Type ℓ where
  ε : Graph A                         -- empty graph 
  node : A → Graph A                  -- single node
  _+_ : Graph A → Graph A → Graph A   -- overlay
  _⇒_ : Graph A → Graph A → Graph A  -- connect

  +-comm : ∀ {x y} → x + y ≡ y + x
  +-assoc : ∀ {x y z} → (x + y) + z ≡ x + (y + z)
  ⇒-identˡ : ∀ {x} → ε ⇒ x ≡ x
  ⇒-identʳ : ∀ {x} → x ⇒ ε ≡ x
  ⇒-assoc : ∀ {x y z} → x ⇒ y ⇒ z ≡ x ⇒ (y ⇒ z)
  ⇒-dist-+ : ∀ {x y z} → x ⇒ (y + z) ≡ x ⇒ y + x ⇒ z
  +-dist-⇒ : ∀ {x y z} → (x + y) ⇒ z ≡ x ⇒ z + y ⇒ z
  ⇒-decomp : ∀ {x y z} → x ⇒ y ⇒ z ≡ x ⇒ y + x ⇒ z + y ⇒ z

  trunc : isSet (Graph A)

