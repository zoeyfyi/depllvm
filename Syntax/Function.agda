--------------------------------------------------------------------------------
-- A function consists of an entry block and a sequence of basic blocks
-- Entry blocks have no predecessors (and thus no phi nodes)
--------------------------------------------------------------------------------

{-# OPTIONS --cubical #-}

module Syntax.Function where

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

private
  variable
    A B C : Typ
    Γ : Context Typ
    Γᵉ : Context Unit
    Δ' : Context BlockContext

infix 5 entry_≔_
infixl 4 _;_≔_

data PreFunction (Γᵖ : Context Typ) (Δ : Context BlockContext) (A : Typ) : Context BlockContext → Type where
  -- entry block can't have predecessors
  -- no predecessors -> no phi nodes
  -- TODO: currently, no nice way to constrain the predecessors, Γᵉ are the outgoing edges
  entry_≔_ : (l : String) → BlockBody l Δ Γᵖ Γ A ε Γᵉ → PreFunction Γᵖ Δ A (ε , l ⦂ blk A Γᵉ Γ)
                                                                             -- ^ we need to be able to reference the entry block in phi nodes,
                                                                             --   but not be able to branch to it (which this doesn't do)
  _;_≔_ : PreFunction Γᵖ Δ A Δ' → (l : String) → Block l Δ Γᵖ Γ A Γᵉ → PreFunction Γᵖ Δ A (Δ' , l ⦂ blk A Γᵉ Γ)


  -- _≔_;_ : (l : String) → Block l Δ Γᵖ Γ A Γᵉ → PreFunction Γᵖ Δ A Δ' → PreFunction Γᵖ Δ A (Δ' , l ⦂ blk A Γᵉ Γ)
  -- _≔_fin : (l : String) → Block l Δ Γᵖ Γ A Γᵉ → PreFunction Γᵖ Δ A (ε , l ⦂ blk A Γᵉ Γ)

record Function (Γᴾ : Context Typ) (A : Typ) : Type where
  constructor func
  field
    {Δ} : Context BlockContext -- Δ contains all the "self-refererential" data we need in each block
                                  -- Type of return
                                  -- Context of labels in block
                                  -- Outgoing edges
                               -- This never needs to be written implicitly since it will always be 
                               -- unified with the inductivly defined analog at all levels, e.g.
                               -- We inductivly build up the context of labels in a block, and the
                               -- base case for a block (the terminator) ensures that this unifys 
                               -- with the block context (or rather an index which will become part
                               -- of the block context
    func : PreFunction Γᴾ Δ A Δ

