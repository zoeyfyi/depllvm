{-# OPTIONS --cubical #-}

module Evaluator.Base where

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

private
  variable
    Γ Γ' Γ'' : Context Typ
    Γᵉ : Context Unit
    Δ Δ' : Context BlockContext
    A B C : Typ
    l : String

-- max : Function (ε , "y" ⦂ int , "x" ⦂ int) int
-- max = func (
--   "entry" ≔ body (
--     "cond" ≔ lte (param "x" s) (param "y" (n s)) ; 
--     exit (brc (label "cond" s) "rx" "ry" (n s) (n (n s)))) ; 
--   "rx" ≔ body (
--     exit (ret (param "x" s))) ; 
--   "ry" ≔ body (
--     exit (ret (param "y" (n s)))) 
--   fin) 

-- TODO: theses should be Dec→Bool when we are ready to reason about correctness
_≤ℕ_ : ℕ → ℕ → Bool
zero ≤ℕ b = true
suc a ≤ℕ zero = false
suc a ≤ℕ suc b = a ≤ℕ b

_≤_ : ℤ → ℤ → Bool 
pos a ≤ pos b = a ≤ℕ b
pos a ≤ negsuc b = false
negsuc a ≤ pos b = true
negsuc a ≤ negsuc b = b ≤ℕ a

eval-value : Model ⟦_⟧ Γ → Model ⟦_⟧ Γ' → Value Γ Γ' A → ⟦ A ⟧
eval-value m m' (` x) = x
eval-value m m' (param l x) = lookup m x
eval-value m m' (label l x) = lookup m' x

record Continuation (Γᵉ : Context Unit) (Δ : Context BlockContext) : Type where
  constructor cont
  field
    {b} : String
    {bc} : BlockContext
    edge : b ⦂ tt ∈ Γᵉ 
    block : b ⦂ bc ∈ Δ

eval-block : ℕ → Model ⟦_⟧ Γ → Model ⟦_⟧ Γ'' → PreBlock l Δ Γ Γ' A Γ'' Γᵉ → (Maybe ⟦ A ⟧) ⊎ Continuation Γᵉ Δ

eval-body : ℕ → Model ⟦_⟧ Γ → Model ⟦_⟧ Γ'' → BlockBody l Δ Γ Γ' A Γ'' Γᵉ → (Maybe ⟦ A ⟧) ⊎ Continuation Γᵉ Δ
eval-body fuel m m' (l ≔ val x ; b) = eval-body fuel m (m' , l ⦂ x) b
eval-body fuel m m' (l ≔ add x y ; b) =
  let v = eval-value m m' x 
      w = eval-value m m' y 
   in eval-body fuel m (m' , l ⦂ (v + w)) b
eval-body fuel m m' (l ≔ lte x y ; b) = 
  let v = eval-value m m' x 
      w = eval-value m m' y 
   in eval-body fuel m (m' , l ⦂ (v ≤ w)) b
eval-body fuel m m' (exit (ret x)) = inl (just (eval-value m m' x))
eval-body fuel m m' (exit (brc x l₁ l₂ l₁∈ l₂∈)) = 
  if eval-value m m' x 
  then inr (cont s l₁∈) 
  else inr (cont (n s) l₂∈)

eval-phi : Model ⟦_⟧ Γ → l ⦂ blk B Γᵉ Γ ∈ Δ → Phi l Δ A → ⟦ A ⟧
eval-phi m s (_ ↦ l [ l∈Γᵉ , l⦂B∈Γ ], p) = lookup m l⦂B∈Γ
eval-phi m s (skip _ [ l∉Γᵉ ], p) = {!   !}
eval-phi m (n x) (_ ↦ l [ x₁ , x₂ ], p) = eval-phi m x p
eval-phi m (n x) (skip _ [ x₁ ], p) = eval-phi m x p

eval-block fuel m m' (l ≔phi x ; b) = eval-block fuel m (m' , l ⦂ {!   !} x) b
eval-block fuel m m' (body x) = eval-body fuel m m' x
-- ... | inl x = x
-- ... | inr c = {!   !}

eval : ℕ → Model ⟦_⟧ Γ → PreFunction Γ Δ A Δ' → l ⦂ blk B Γᵉ Γ' ∈ Δ' → (Maybe ⟦ A ⟧) ⊎ Continuation Γᵉ Δ
eval fuel m (entry l ≔ x) s = eval-body fuel m ε x
eval fuel m (b ; l ≔ x) s = eval-block fuel m ε x
eval fuel m (b ; l ≔ x) (n p) = eval fuel m b p
-- eval fuel m (_ ≔ b ; f) s = eval-block fuel m ε b
-- eval fuel m (_ ≔ b fin) s = eval-block fuel m ε b
-- eval fuel m (_ ≔ x ; f) (n p) = eval fuel m f p 

eval-fun : ℕ → Model ⟦_⟧ Γ → (f : Function Γ A) → l ⦂ blk B Γᵉ Γ' ∈ (Function.Δ f) → Maybe ⟦ A ⟧
eval-fun fuel m (func f) p with eval fuel m f p
... | inl x = x
eval-fun zero m (func f) p | inr x = nothing
eval-fun (suc fuel) m (func f) p | inr x = eval-fun fuel m (func f) (Continuation.block x) 