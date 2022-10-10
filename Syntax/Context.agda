{-# OPTIONS --cubical #-}

module Syntax.Context where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Data.Prod
open import Cubical.Data.Sum
open import Cubical.Data.Nat
open import Agda.Builtin.String
open import Cubical.HITs.ListedFiniteSet
open import Cubical.HITs.PropositionalTruncation renaming (rec to prec)
open import Cubical.Data.Empty renaming (rec to ⊥-elim)

infixl 5 _,_⦂_

private
  variable
    ℓ : Level
    A B : Type ℓ
    l₁ l₂ l₃ : String

data Context {ℓ} (A : Type ℓ) : Type ℓ where
  ε : Context A
  _,_⦂_ : Context A → String → A → Context A

private
  variable
    Γ : Context A

length : Context A → ℕ
length ε = 0
length (Γ , x ⦂ A) = suc (length Γ)

data _⦂_∈_ {ℓ} {A : Type ℓ} : String → A → Context A → Type ℓ where
  s : ∀ {A} → l₁ ⦂ A ∈ (Γ , l₁ ⦂ A)
  n : ∀ {A B} → l₁ ⦂ A ∈ Γ → l₁ ⦂ A ∈ (Γ , l₂ ⦂ B)

