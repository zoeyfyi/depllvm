{-# OPTIONS --cubical #-}

module Syntax2.BlockInfo where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Data.Prod
open import Cubical.Data.Sum
open import Cubical.Data.Nat
open import Cubical.Data.List
open import Agda.Builtin.String
open import Cubical.HITs.ListedFiniteSet
open import Cubical.HITs.PropositionalTruncation renaming (rec to prec)
open import Cubical.Data.Empty renaming (rec to ⊥-elim)

open import Syntax2.Type
open import Syntax2.Context

record BlockInfo : Type where
  constructor blk
  field
    btyp : Typ
    bctx : Context Typ
    -- bpost : Context Unit

open BlockInfo public

