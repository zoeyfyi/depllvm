{-# OPTIONS --cubical #-}

module Syntax2.Instruction where

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

open import Syntax2.Context
open import Syntax2.Type
open import Syntax2.Value
open import Syntax2.BlockInfo

private
  variable
    A B C R : Typ
    Γ Γ' Γᵖ : Context Typ
    Γⁱⁿ Γᵒᵘᵗ : Context Unit

data IKind : Type where
  phi : IKind
  inst : IKind
  term : Typ → Context Unit → IKind

-- Γᵖ : Function parameter context
-- Γᵉ : Predecessors
-- R : Function return type
-- Typ : Type of instruction result
-- IKind : Kind of instruction
data Instruction (b : String) (Γᵖ Γ : Context Typ) (Γᵉ : Context Unit) (Δ : Context (Context Typ)) : Typ → IKind → Type

-- Type constructors for different instruction kinds

Phi Inst : String → Context Typ → Context Typ → Context Unit → Context (Context Typ) → Typ → Type
Inst b Γᵖ Γ Γᵉ Δ A = Instruction b Γᵖ Γ Γᵉ Δ A inst
Phi b Γᵖ Γ Γᵉ Δ A = Instruction b Γᵖ Γ Γᵉ Δ A phi

Term : String → Context Typ → Context Typ → Context Unit → Context (Context Typ) → Typ → Typ → Context Unit → Type
Term b Γᵖ Γ Γᵉ Δ R A Γᵉ' = Instruction b Γᵖ Γ Γᵉ Δ A (term R Γᵉ')

data PhiData (b : String) (Γᵖ Γ : Context Typ) (Δ : Context (Context Typ)) (A : Typ) : Context Unit → Type where
  ε : PhiData b Γᵖ Γ Δ A ε
  _,_[_]↦_ : PhiData b Γᵖ Γ Δ A Γⁱⁿ 
           → (l : String)                     -- incoming block 
           → b ⦂ tt ∈ Γᵒᵘᵗ                      -- l is predecessor of b
           → l ⦂ Γ' ∈ Δ
           → Value l Γᵖ Γ' A                 -- value (possibly in block l)
           → PhiData b Γᵖ Γ Δ A (Γⁱⁿ , l ⦂ tt)

data Instruction b Γᵖ Γ Γⁱⁿ Δ where

  ------------------------
  -- Values
  ------------------------

  -- this doesnt exist in LLVM
  -- ` : (A : Typ) → ⟦ A ⟧ → Inst b Γᵖ Γ Γⁱⁿ Δ R A

  ------------------------
  -- Instructions
  ------------------------

  phi : PhiData b Γᵖ Γ Δ A Γⁱⁿ → Phi b Γᵖ Γ Γⁱⁿ Δ A 

  -- add to integers
  -- TODO: add support for other types
  add : Value b Γᵖ Γ int → Value b Γᵖ Γ int → Inst b Γᵖ Γ Γⁱⁿ Δ int

  -- less than or equal to
  -- this doesn't exist in LLVM, instead there is a icmp instruction
  -- with different "condition codes"
  lte : Value b Γᵖ Γ int → Value b Γᵖ Γ int → Inst b Γᵖ Γ Γⁱⁿ Δ bool  

  ------------------------
  -- Terminators
  ------------------------

  -- return value of function
  ret : (R : Typ) → Value b Γᵖ Γ R → Term b Γᵖ Γ Γⁱⁿ Δ R void ε

  -- branch to label
  -- In LLVM, brl and brc bellow are two forms of the same instruction (br)
  -- We can replicate that by:
  --   ∙ adding label to the typs
  --   ∙ new type BrArgs : Typ → Type
  --   ∙ two constructors corresponding to the syntax of the different forms
  brl : (BlockLabel Δ) → Term b Γᵖ Γ Γⁱⁿ Δ R void (ε , b ⦂ tt)

  -- branch on condition
  brc : Value b Γᵖ Γ bool → (v : BlockLabel Δ) → (w : BlockLabel Δ) → Term b Γᵖ Γ Γⁱⁿ Δ R void (ε , v .block ⦂ tt , w .block ⦂ tt)




-- With some careful choice of constructors we can get very close to LLVM syntax

-- data TypedValue (Γᵖ Γ : Context Typ) : Typ → Type where
--   label : String → TypedValue Γᵖ Γ label
--   i1 : Value Γᵖ Γ bool → TypedValue Γᵖ Γ bool

-- data BrArgs (Γᵖ Γ : Context Typ) : Type where
--   label : (l : String) → BrArgs Γᵖ Γ
--   _,_,_ : TypedValue Γᵖ Γ bool → TypedValue Γᵖ Γ label → TypedValue Γᵖ Γ label → BrArgs Γᵖ Γ