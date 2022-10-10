-- Based on: https://github.com/algebraic-graphs/agda
{-# OPTIONS --cubical #-}

module Graph.Sets.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Prod
open import Cubical.HITs.ListedFiniteSet
open import Cubical.Relation.Nullary
open import Util.LFSet.Discrete

private
  variable
    ℓ : Level
    A : Type ℓ

record Graph {ℓ} (A : Type ℓ) : Type ℓ where
  constructor _,_
  field
    nodes : LFSet A
    edges : LFSet (A × A)
open Graph

postulate discrete× : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → Discrete A → Discrete B → Discrete (A × B)

postulate isSetGraph : ∀ {ℓ} {A : Type ℓ} → isSet (Graph A)

discreteGraph : Discrete A → Discrete (Graph A)
discreteGraph disA (ns₁ , es₁) (ns₂ , es₂) with discreteLFSet disA ns₁ ns₂ | discreteLFSet (discrete× disA disA) es₁ es₂
... | yes p | yes q = yes (λ i → p i , q i)
... | yes p | no ¬q = no (λ x → ¬q (cong edges x))
... | no ¬p | q = no (λ x → ¬p (cong nodes x))

overlay : Graph A → Graph A → Graph A
overlay (ns₁ , es₁) (ns₂ , es₂) = ns₁ ++ ns₂ , es₁ ++ es₂

connect : Graph A → Graph A → Graph A
connect (ns₁ , es₁) (ns₂ , es₂) = ns₁ ++ ns₂ , es₁ ++ es₂ ++ (cart-product ns₁ ns₂)

overlay-comm : (x y : Graph A) → overlay x y ≡ overlay y x
overlay-comm (ns₁ , es₁) (ns₂ , es₂) = cong₂ _,_ (comm-++ ns₁ ns₂) (comm-++ es₁ es₂)
