{-# OPTIONS --cubical #-}

module Util.LFSet.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Data.Prod
open import Cubical.Data.Sum
open import Cubical.HITs.ListedFiniteSet
open import Cubical.HITs.PropositionalTruncation renaming (rec to prec)
open import Cubical.Data.Empty renaming (rec to ⊥-elim)


private
  variable
    ℓ : Level
    A : Type ℓ

++-identʳ : (xs : LFSet A) → xs ++ [] ≡ xs
++-identʳ = PropElim.f refl (λ x p → cong (x ∷_) p) (λ _ → trunc _ _)

unpair : LFSet (A × A) → LFSet A
unpair [] = []
unpair ((x , y) ∷ xs) = x ∷ y ∷ unpair xs
unpair (dup (x , y) xs i) = (
  x ∷ y ∷ x ∷ y ∷ unpair xs  ≡⟨ cong (x ∷_) (comm y x _) ⟩ 
  x ∷ x ∷ y ∷ y ∷ unpair xs  ≡⟨ dup x _ ⟩ 
  x ∷ y ∷ y ∷ unpair xs      ≡⟨ cong (x ∷_) (dup y _) ⟩ 
  x ∷ y ∷ unpair xs          ∎) i
unpair (comm (x , y) (a , b) xs i) = (
  x ∷ y ∷ a ∷ b ∷ unpair xs ≡⟨ comm x y _ ⟩ 
  y ∷ x ∷ a ∷ b ∷ unpair xs ≡⟨ cong (y ∷_) (comm x a _) ⟩ 
  y ∷ a ∷ x ∷ b ∷ unpair xs ≡⟨ comm y a _ ⟩ 
  a ∷ y ∷ x ∷ b ∷ unpair xs ≡⟨ cong (a ∷_) (comm y x _) ⟩ 
  a ∷ x ∷ y ∷ b ∷ unpair xs ≡⟨ cong (λ xs → a ∷ x ∷ xs) (comm y b _) ⟩ 
  a ∷ x ∷ b ∷ y ∷ unpair xs ≡⟨ cong (a ∷_) (comm x b _) ⟩ 
  a ∷ b ∷ x ∷ y ∷ unpair xs ∎) i
unpair (trunc xs ys p q i j) = trunc (unpair xs) (unpair ys) (cong unpair p) (cong unpair q) i j

