{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary

module Util.LFSet.Discrete {ℓ} {A : Type ℓ} (disA : Discrete A) where

open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Data.Prod
open import Cubical.Data.Sum
open import Cubical.HITs.ListedFiniteSet
open import Cubical.HITs.PropositionalTruncation renaming (rec to prec)
open import Cubical.Data.Empty renaming (rec to ⊥-elim)

private
  variable
    ℓ₁ ℓ₂ : Level 
    x y z : A
    xs ys : LFSet A

¬empty∈ : ⟨ x ∈ [] ⟩ → ⊥
¬empty∈ ()

emptyIn : ∀ (xs : LFSet A) → (∀ x → ¬ ⟨ x ∈ xs ⟩) → xs ≡ []
emptyIn = PropElim.f (λ _ → refl) (λ x p q → ⊥-elim (q x ∣ (inl ∣ refl ∣₁) ∣₁)) λ xs → isPropΠ λ _ → trunc _ _

in-cons : ∀ xs → ⟨ x ∈ xs ⟩ → xs ≡ x ∷ xs
in-cons = PropElim.f (λ ()) (λ x p q → prec (trunc _ _) (λ { (inl x≡y) → prec (trunc _ _) (λ x≡y → sym (cong (_∷ _) x≡y ∙ dup x _)) x≡y
                                                           ; (inr x) → sym (comm _ _ _ ∙ cong (_ ∷_) (sym (p x))) }) q) (λ _ → isPropΠ (λ _ → trunc _ _))

-- (x ∷ xs) ≡ ys
-- x ∈ xs
-- x ∈ ys

record _↔_ (A : Type ℓ₁) (B : Type ℓ₂) : Type (ℓ-max ℓ₁ ℓ₂) where
  field
    to : A → B
    from : B → A
open _↔_

postulate ↔-sym : ∀ {A : Type ℓ₁} {B : Type ℓ₂} → A ↔ B ≡ B ↔ A
-- ↔-sym = {!   !}

⊥₁ : ∀ ℓ → hProp ℓ
⊥₁ _ = Lift ⊥ , isOfHLevelLift 1 isProp⊥

¬⊥₁ : ∀ ℓ → ¬ ⟨ ⊥₁ ℓ ⟩
¬⊥₁ _ ()

postulate univEq : {A : Type ℓ} → ∀ (xs ys : LFSet A) → (∀ x → ⟨ x ∈ xs ⟩ ↔ ⟨ x ∈ ys ⟩) → xs ≡ ys
postulate _∈?_ : (x : A) → (xs : LFSet A) → Dec ⟨ x ∈ xs ⟩

postulate discreteLFSet : Discrete (LFSet A)
-- discreteLFSet xs ys = {!   !}


-- univEq {ℓ = ℓ} {A = A} disA = PropElim.f (λ ys → lemma1) lemma2
--   (λ _ → isPropΠ2 (λ _ _ → trunc _ _))
--   where
--   lemma1 : (∀ x → ⟨ ⊥₁ ℓ ⟩ ↔ ⟨ x ∈ ys ⟩) → [] ≡ ys
--   lemma1 p = sym (emptyIn _ (λ x x∈ys → ¬⊥₁ _ (from (p x) x∈ys)))

--   -- lemma3 : (x₁ : A) {xs : LFSet A} →
--   --     (((y : A) →
--   --       ⟨
--   --       (y ∈ (x ∷ xs₁))
--   --       ⟩
--   --       ↔ ⟨ y ∈ xs ⟩) →
--   --      x ∷ xs₁ ≡ xs) →
--   --     ((y : A) →
--   --      ⟨
--   --      (y Cubical.Functions.Logic.≡ₚ x) Cubical.Functions.Logic.⊔
--   --      (y ∈ xs₁)
--   --      ⟩
--   --      ↔
--   --      ⟨
--   --      (y Cubical.Functions.Logic.≡ₚ x₁) Cubical.Functions.Logic.⊔
--   --      (y ∈ xs)
--   --      ⟩) →
--   --     x ∷ xs₁ ≡ x₁ ∷ xs
--   -- lemma3 = ?
--   postulate lemma3 : ∀ {x xs ys} 
--          → (y : A) 
--          → ((∀ y → ⟨ y ∈ (x ∷ xs) ⟩ ↔ ⟨ y ∈ ys ⟩) → x ∷ xs ≡ ys) 
--          → (∀ z → ⟨ z ∈ (x ∷ xs) ⟩ ↔ ⟨ z ∈ (y ∷ ys) ⟩)
--          → (∀ ys → (∀ y → ⟨ y ∈ xs ⟩ ↔ ⟨ y ∈ ys ⟩) → xs ≡ ys)
--          → x ∷ xs ≡ y ∷ ys
--   -- lemma3 {x = x} {xs} {ys} y p q r with disA x y 
--   -- ... | yes x≡y = {!   !}
--   -- ... | no ¬x≡y = {!   !}
--   --   where 
--   --   lemma4 : ∀ y → ⟨ y ∈ (x ∷ xs) ⟩ ↔ ⟨ y ∈ ys ⟩
--   --   lemma4 y with disA x y 
--   --   ... | yes p = record { to = λ _ → {!   !} ; from = {!   !} }
--   --   ... | no ¬p = {!   !}
--     -- let foo = p {!   !} in {!   !}


  
--   -- with disA x y 
--   -- ... | yes x≡y = {!   !}
--   -- ... | no ¬p = {!   !}

--   -- p : ((y₁ : A) →
--   --         ⟨
--   --         (y₁ Cubical.Functions.Logic.≡ₚ x) Cubical.Functions.Logic.⊔
--   --         (y₁ ∈ xs)
--   --         ⟩
--   --         ↔ ⟨ y₁ ∈ xs₁ ⟩) →
--   --        x ∷ xs ≡ xs₁

--   lemma2 : ∀ x {xs} 
--     → (∀ ys → (∀ y → ⟨ y ∈ xs ⟩ ↔ ⟨ y ∈ ys ⟩) → xs ≡ ys) 
--     → (ys : LFSet A) 
--     → ((y : A) → ⟨ y ∈ (x ∷ xs) ⟩ ↔ ⟨ y ∈ ys ⟩) 
--     → x ∷ xs ≡ ys
--   lemma2 x {xs} r = PropElim.f 
--     (λ q → sym (lemma1 λ y → transport ↔-sym (q y))) 
--     (λ y {ys} p q → lemma3 {x = x} {xs = xs} {ys = ys} y p q r) 
--     (λ _ → isPropΠ (λ _ → trunc _ _))
  
--     -- let x∈ys = to (q x) ∣ (inl ∣ refl ∣₁) ∣₁
--     --  in {!   !}

-- -- PropElim.f 
--   -- ?
--   -- (λ x p → sym (emptyIn _ (λ x x∈ys → ¬empty∈ {x = x} (p x x∈ys)))) 
--   -- {!   !}
--   -- (λ { x {xs} p q r → PropElim.f {B = λ ys → x ∷ xs ≡ ys} {!   !} (λ y {zs} x∷xs≡zs → {!   !}) (λ _ → trunc _ _) ys })
--   -- (λ _ → isPropΠ2 (λ _ _ → trunc _ _))
  
--   -- where
--   -- lemma : (x y : A) → x ∷ xs ≡ x ∷ y ∷ xs
--   -- lemma {xs = xs} x y with disA x y
--   -- ... | yes p = 
--   --   x ∷ xs      ≡⟨ sym (dup x xs) ⟩  
--   --   x ∷ x ∷ xs  ≡⟨ cong (λ a → x ∷ a ∷ xs) p ⟩  
--   --   x ∷ y ∷ xs  ∎
--   -- ... | no ¬p = {!   !} 