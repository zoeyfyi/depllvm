{-# OPTIONS --cubical #-}

module Syntax2.Type where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Int hiding (_+_)
open import Cubical.Data.Fin
open import Cubical.Data.Bool using (Bool; true; false)
open import Agda.Builtin.String
open import Cubical.HITs.ListedFiniteSet
open import Cubical.HITs.PropositionalTruncation renaming (rec to prec)
open import Cubical.Data.Empty renaming (rec to ⊥-elim)
open import Cubical.Relation.Nullary

data Typ : Type where
  int : Typ
  bool : Typ
  void : Typ

⟦_⟧ : Typ → Type
⟦ int ⟧ = ℤ
⟦ bool ⟧ = Bool
⟦ void ⟧ = ⊥

TypIso : Iso Typ (Fin 3)
TypIso = iso to from to-from from-to
  where
  to : Typ → Fin 3
  to int = fzero
  to bool = fsuc fzero
  to void = fsuc (fsuc fzero)


  ¬s<z : ∀ {n} → ¬ (suc n < zero)
  ¬s<z {n} (x , p) = snotz (sym (+-suc x (1 + n)) ∙ p)

  from : Fin 3 → Typ
  from (zero , p) = int
  from (suc zero , p) = bool
  from (suc (suc zero) , p) = void
  from (suc (suc (suc x)) , p) = ⊥-elim (¬-<-zero (pred-≤-pred (pred-≤-pred (pred-≤-pred p))))

  to-from : ∀ x → to (from x) ≡ x
  to-from (zero , p) = ΣPathP (refl , isProp≤ _ _)
  to-from (suc zero , p) = ΣPathP (refl , isProp≤ _ _)
  to-from (suc (suc zero) , p) = ΣPathP (refl , isProp≤ _ _)
  to-from (suc (suc (suc x)) , p) = ⊥-elim (¬-<-zero (pred-≤-pred (pred-≤-pred (pred-≤-pred p))))

  from-to : ∀ x → from (to x) ≡ x
  from-to int = refl
  from-to bool = refl
  from-to void = refl

discreteTyp : Discrete Typ
discreteTyp = sectionDiscrete (TypIso .Iso.inv) (TypIso .Iso.fun) (TypIso .Iso.leftInv) discreteFin
