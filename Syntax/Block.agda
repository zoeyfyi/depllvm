{-# OPTIONS --cubical #-}

module Syntax.Block where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Data.Prod
open import Cubical.Data.Sum
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Relation.Nullary
open import Agda.Builtin.String
open import Cubical.HITs.ListedFiniteSet
open import Cubical.HITs.PropositionalTruncation renaming (rec to prec)
open import Cubical.Data.Empty renaming (rec to ⊥-elim)

open import Syntax.Type
open import Syntax.Context
open import Syntax.Instruction
open import Syntax.BlockContext

infixr 5 _≔_;_

private
  variable
    Γ Γ' : Context Typ
    Γᵉ : Context Unit
    Δ Δ' : Context BlockContext
    A B C : Typ

data BlockBody (b : String) (Δ : Context BlockContext) (Γᵖ Γ : Context Typ)
  : Typ
  → Context Typ  -- value context
  → Context Unit  -- outgoing edges
  → Type 
  where 
  _≔_;_ : (l : String) → Instruction Γᵖ Γ' A → BlockBody b Δ Γᵖ Γ B (Γ' , l ⦂ A) Γᵉ → BlockBody b Δ Γᵖ Γ B Γ' Γᵉ
  exit 
    : Terminator b Δ Γᵖ Γ A Γᵉ 
    → BlockBody b Δ Γᵖ Γ A Γ Γᵉ
                --  ^   ^ inductivly defined must match global at the end

data Phi (b : String)
  : Context BlockContext
  → Typ
  → Type
  where
  ε : Phi b ε A
  _↦_[_,_],_ 
    : (b' l : String)                     -- incoming block and a label in that block
    → b ⦂ tt ∈ Γᵉ                          -- proof of edge b → b'
    → l ⦂ A ∈ Γ                            -- proof l is in incoming block
    → Phi b Δ' A 
    → Phi b (Δ' , b' ⦂ blk A Γᵉ Γ) A
  skip_[_],_ 
    : (b' : String)                       -- block that we are skipping
    → ¬ b ⦂ tt ∈ Γᵉ                        -- proof that there is no edge b → b'
    → Phi b Δ' A 
    → Phi b (Δ' , b' ⦂ blk B Γᵉ Γ) A

-- Phi : (b : String) (Δ : Context BlockContext) → Typ → Type
-- Phi b Δ A = PrePhi b Δ A

-- A preblock is a list of phi nodes, followed by a block body
data PreBlock (b : String) (Δ : Context BlockContext) (Γᵖ Γ : Context Typ)
  : Typ 
  → Context Typ  -- inductivly defined value context
  → Context Unit  -- outgoing edges
  → Type 
  where 
  _≔phi_;_ : (l : String) → Phi b Δ A → PreBlock b Δ Γᵖ Γ A (Γ' , l ⦂ A) Γᵉ → PreBlock b Δ Γᵖ Γ A Γ' Γᵉ
  body : BlockBody b Δ Γᵖ Γ A Γ' Γᵉ → PreBlock b Δ Γᵖ Γ A Γ' Γᵉ

-- A block is a preblock that starts with the empty context
Block 
  : String                -- name of the block
  → Context BlockContext  -- all blocks
  → Context Typ           -- parameter context
  → Context Typ           -- final value context
  → Typ
  → Context Unit          -- outgoing edges
  → Type
Block b Δ Γᵖ Γ A Γᵉ = PreBlock b Δ Γᵖ Γ A ε Γᵉ

