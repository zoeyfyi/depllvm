{-# OPTIONS --cubical #-}

module Evaluator.Examples where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Data.Prod
open import Cubical.Data.Sum
open import Cubical.Data.Bool using (Bool; true; false; if_then_else_)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Int using (ℤ; _+_; pos; negsuc)
open import Cubical.Data.Unit
open import Cubical.Data.Maybe
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

open import Evaluator.Model

-- Approximate C version
--
-- int min(int x, int y) {
--     bool cond = x < y;
--     if (cond) {
--         return x;
--     } else {
--         return y;
--     }
-- }
min : Function (ε , "y" ⦂ int , "x" ⦂ int) int
min = func (((
  entry "entry" ≔ 
    "cond" ≔ (lte (param "x" s) (param "y" (n s))) ; 
    exit (brc (label "cond" s) "rx" "ry" (n s) s)) ; 
  "rx" ≔ body (
    exit (ret (param "x" s)))) ; 
  "ry" ≔ body (
    exit (ret (param "y" (n s)))))


-- max = func (
--   "entry" ≔ body (
--     "cond" ≔ lte (param "x" s) (param "y" (n s)) ; 
--     exit (brc (label "cond" s) "rx" "ry" (n s) (n (n s)))) ; 
--   "rx" ≔ body (
--     exit (ret (param "x" s))) ; 
--   "ry" ≔ body (
--     exit (ret (param "y" (n s)))) 
--   fin)  