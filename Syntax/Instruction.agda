{-# OPTIONS --cubical #-}

module Syntax.Instruction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Data.Prod
open import Cubical.Data.Sum
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.List
open import Agda.Builtin.String
open import Cubical.HITs.ListedFiniteSet
open import Cubical.HITs.PropositionalTruncation renaming (rec to prec)
open import Cubical.Data.Empty renaming (rec to ⊥-elim)

open import Syntax.Context
open import Syntax.Type
open import Syntax.Value
open import Syntax.BlockContext

private
  variable
    Γ Γᵖ : Context Typ
    A B C : Typ

data Instruction (Γᵖ : Context Typ) (Γ : Context Typ) : Typ → Type where
  val : ⟦ A ⟧ → Instruction Γᵖ Γ A 
  add : Value Γᵖ Γ int → Value Γᵖ Γ int → Instruction Γᵖ Γ int
  lte : Value Γᵖ Γ int → Value Γᵖ Γ int → Instruction Γᵖ Γ bool

data Terminator 
  (b : String)                  -- label of current block
  (Δ : Context BlockContext)  -- all blocks and there outgoing labels
  (Γᵖ Γ : Context Typ)             -- label in the current block
  (A : Typ)
  : 
  Context Unit →                 -- outgoing edges
  Type where
  ret : Value Γᵖ Γ A → Terminator b Δ Γᵖ Γ A ε
  brc : ∀ {bc bc'} → Value Γᵖ Γ bool 
      → (l₁ : String) -- if true block
      → (l₂ : String) -- if false block
      → l₁ ⦂ bc ∈ Δ
      → l₂ ⦂ bc' ∈ Δ
      → Terminator b Δ Γᵖ Γ A (ε , l₂ ⦂ tt , l₁ ⦂ tt)