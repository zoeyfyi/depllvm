{-# OPTIONS --cubical #-}

module Evaluator.Model where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Data.Prod
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Agda.Builtin.String
open import Cubical.HITs.ListedFiniteSet
open import Cubical.HITs.PropositionalTruncation renaming (rec to prec)
open import Cubical.Data.Empty renaming (rec to ⊥-elim)

open import Syntax.Type
open import Syntax.Context
open import Syntax.Block
open import Syntax.BlockContext
open import Syntax.Instruction
open import Syntax.Function
open import Syntax.Value

private
  variable
    ℓ : Level
    A : Type ℓ
    a : A
    F : A → Type ℓ
    Γ : Context A
    l : String

data Model {ℓ} {A : Type ℓ} (F : A → Type ℓ) : Context A → Type ℓ where
  ε : Model F ε
  _,_⦂_ : ∀ {Γ} → Model F Γ → (l : String) → {a : A} (v : F a) → Model F (Γ , l ⦂ a)

lookup : Model F Γ → l ⦂ a ∈ Γ → F a
lookup (m , _ ⦂ v) s = v
lookup (m , _ ⦂ v) (n p) = lookup m p
