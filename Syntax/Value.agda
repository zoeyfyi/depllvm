{-# OPTIONS --cubical #-}

module Syntax.Value where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Data.Prod
open import Cubical.Data.Sum
open import Cubical.Data.Nat
open import Agda.Builtin.String
open import Cubical.HITs.ListedFiniteSet
open import Cubical.HITs.PropositionalTruncation renaming (rec to prec)
open import Cubical.Data.Empty renaming (rec to ⊥-elim)

open import Syntax.Type
open import Syntax.Context

private
  variable
    A B C : Typ

data Value (Γᵖ : Context Typ) (Γ : Context Typ) : Typ → Type where
  `_ : ⟦ A ⟧ → Value Γᵖ Γ A
  param : (l : String) → l ⦂ A ∈ Γᵖ → Value Γᵖ Γ A
  label : (l : String) → l ⦂ A ∈ Γ → Value Γᵖ Γ A

