{-# OPTIONS --cubical #-}

module Syntax.Type where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Data.Prod
open import Cubical.Data.Sum
open import Cubical.Data.Int
open import Cubical.Data.Bool
open import Agda.Builtin.String
open import Cubical.HITs.ListedFiniteSet
open import Cubical.HITs.PropositionalTruncation renaming (rec to prec)
open import Cubical.Data.Empty renaming (rec to ⊥-elim)


data Typ : Type where
  int : Typ
  bool : Typ

⟦_⟧ : Typ → Type
⟦ int ⟧ = ℤ
⟦ bool ⟧ = Bool

