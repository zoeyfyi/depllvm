{-# OPTIONS --cubical #-}

module Syntax2.Value where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Data.Prod
open import Cubical.Data.Sum
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Agda.Builtin.String
open import Cubical.HITs.ListedFiniteSet
open import Cubical.HITs.PropositionalTruncation renaming (rec to prec)
open import Cubical.Data.Empty renaming (rec to ⊥-elim)

open import Syntax2.Type
open import Syntax2.Context
open import Syntax2.BlockInfo

private
  variable
    b : String
    A B C : Typ
    Γᵖ Γ : Context Typ
    Γᵒᵘᵗ : Context Unit
    Δ : Context (Context Typ)

data Value (b : String) (Γᵖ : Context Typ) (Γ : Context Typ) : Typ → Type where
  `_ : ⟦ A ⟧ → Value b Γᵖ Γ A
  param : (l : String) → l ⦂ A ∈ Γᵖ → Value b Γᵖ Γ A
  label : (l : String) → l ⦂ A ∈ Γ → Value b Γᵖ Γ A
  -- block : ∀ (l : String) 
  --       → l ⦂ tt ∈ Γᵒᵘᵗ     -- l is in outgoing edges (valid branch target)
  --       → Value b Γᵖ Γ Γᵒᵘᵗ label

record BlockLabel (Δ : Context (Context Typ)) : Type where
  constructor _,_
  field 
    block : String
    {bΓ} : Context Typ
    in-func : block ⦂ bΓ ∈ Δ
open BlockLabel public

-- Smart constructor for Value
-- Agda will check if l is in parameters, or in block context
%_ : (l : String) → {True (dec⊎ (dec-∈ discreteTyp l A Γᵖ) (dec-∈ discreteTyp l A Γ))} → Value b Γᵖ Γ A
%_ l {p} with toWitness p 
... | inl x = param l x
... | inr x = label l x

%b_ : (b : String) → {True (dec-∃∈ b Δ)} → BlockLabel Δ
%b_ b {p} with toWitness p 
... | Γ , p = b , p

-- record InLabel (Γⁱⁿ : Context Unit) (Δ : Context (Context Typ)) (A : Typ) : Type where
--   field
--     l : String
--     incoming : l ⦂ tt ∈ Γⁱⁿ
--     {lΓ} : Context Typ
--     inctx : l ⦂ lΓ ∈ Δ
--     {l'} : String
--     lab : l' ⦂ A ∈ lΓ

-- lname : Value b Γᵖ Γ Γᵒᵘᵗ label → String
-- lname (block l _) = l

-- labelname (param l x) = {!   !}
-- labelname (label l x) = {!   !}
-- labelname (block l x x₁) = {!   !}