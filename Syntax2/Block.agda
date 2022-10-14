{-# OPTIONS --cubical #-}

module Syntax2.Block where

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

open import Syntax2.Type
open import Syntax2.Context
open import Syntax2.Instruction
open import Syntax2.BlockInfo

infixr 5 _;_≔_

private
  variable
    A B C : Typ
    Γ Γ' : Context Typ
    Γⁱⁿ Γᵒᵘᵗ : Context Unit

-- block
-- <phi> ;
-- <phi> ;;
-- <inst> ;;
-- <term>

data PreBlockEdges (b : String) (Γᵖ : Context Typ) (Δ : Context (Context Typ)) : Context Unit → Context Typ → Type where
  preds : (Γⁱⁿ : Context Unit) → PreBlockEdges b Γᵖ Δ Γⁱⁿ ε
  _;_≔_ : PreBlockEdges b Γᵖ Δ Γⁱⁿ Γ → (l : String) → Phi b Γᵖ Γ Γⁱⁿ Δ A → PreBlockEdges b Γᵖ Δ Γⁱⁿ (Γ , l ⦂ A)

data PreBlockBody (b : String) (Γᵖ : Context Typ) (Δ : Context (Context Typ)) : Context Unit → Context Typ → Type where
  _;; : PreBlockEdges b Γᵖ Δ Γⁱⁿ Γ → PreBlockBody b Γᵖ Δ Γⁱⁿ Γ
  _;_≔_ : PreBlockBody b Γᵖ Δ Γⁱⁿ Γ → (l : String) → Inst b Γᵖ Γ Γⁱⁿ Δ A → PreBlockBody b Γᵖ Δ Γⁱⁿ (Γ , l ⦂ A)
  
data PreBlock (b : String) (Γᵖ : Context Typ) (Δ : Context (Context Typ)) (R : Typ) : Context Unit → Context Unit → Context Typ → Type where
  _;;_ : PreBlockBody b Γᵖ Δ Γⁱⁿ Γ → Term b Γᵖ Γ Γⁱⁿ Δ R A Γᵒᵘᵗ → PreBlock b Γᵖ Δ R Γⁱⁿ Γᵒᵘᵗ Γ


  -- _;_ : PreBlockBody b Γᵖ Δ R A Γⁱⁿ Γᵒᵘᵗ Γ → Term b Γᵖ Γ {!   !} {!   !} {!   !} {!   !} {!   !} → PreBlockBody b Γᵖ Δ R A Γⁱⁿ Γᵒᵘᵗ Γ
  
  -- _≔_ : ∀ {k} (l : String) 
  --     → Instruction b Γᵖ Γ Γⁱⁿ Δ A k 
  --     → PreBlock b Γᵖ Δ R A Γⁱⁿ Γᵒᵘᵗ (ε , l ⦂ A) k
  -- _;_≔_ : ∀ {k} 
  --       → PreBlock b Γᵖ Δ R A Γⁱⁿ Γᵒᵘᵗ Γ k
  --       → (l : String)
  --       → Instruction b Γᵖ Γ Γⁱⁿ Δ A k
  --       → PreBlock b Γᵖ Δ R A Γⁱⁿ Γᵒᵘᵗ (Γ , l ⦂ A) k


  -- _≔_;_ : ∀ {k} (l : String) 
  --       → Phi b Γᵖ Γ Γⁱⁿ Δ R A 
  --       → PreBlock b Γᵖ Δ R A Γⁱⁿ Γᵒᵘᵗ (Γ , l ⦂ A) k 
  --       → PreBlock b Γᵖ Δ R A Γⁱⁿ Γᵒᵘᵗ Γ phi
  -- _≔_;'_ : (l : String) 
  --        → Inst b Γᵖ Γ Γⁱⁿ Δ R A 
  --        → PreBlock b Γᵖ Δ R A Γⁱⁿ Γᵒᵘᵗ {!   !} inst 
  --        → PreBlock b Γᵖ Δ R A Γⁱⁿ Γᵒᵘᵗ {!   !} inst
  -- _;; : Term b Γᵖ Γ Γⁱⁿ Δ R A Γᵒᵘᵗ → PreBlock b Γᵖ Δ R A Γⁱⁿ Γᵒᵘᵗ {!   !} inst

-- EntryBlock : String → Context Typ → Context Typ → Context (Context Typ) → Typ → Typ → Context Unit → Type
-- EntryBlock b Γᵖ Γ Δ R A Γᵒᵘᵗ = PreBlockBody b Γᵖ Δ R A ε Γᵒᵘᵗ Γ

-- Block : String → Context Typ → Context Typ → Context (Context Typ) → Typ → Typ → Context Unit → Context Unit → Type
-- Block b Γᵖ Γ Δ R A Γⁱⁿ Γᵒᵘᵗ = PreBlockBody b Γᵖ Δ R A Γⁱⁿ Γᵒᵘᵗ Γ 