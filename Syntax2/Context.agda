{-# OPTIONS --cubical #-}

module Syntax2.Context where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Data.Prod
open import Cubical.Data.Sum
open import Cubical.Data.Nat
open import Cubical.HITs.ListedFiniteSet
open import Cubical.HITs.PropositionalTruncation renaming (rec to prec)
open import Cubical.Data.Empty renaming (rec to ⊥-elim)
open import Cubical.Relation.Nullary
open import Util.String.Base

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

dec-∈ : Discrete A → (l : String) → (a : A) → (Γ : Context A) → Dec (l ⦂ a ∈ Γ)
dec-∈ discA l a ε = no (λ ())
dec-∈ discA l a (Γ , m ⦂ b) with discreteString l m | discA a b | dec-∈ discA l a Γ 
... | yes p | yes q | r = yes (transport (cong₂ (λ m b → l ⦂ a ∈ (Γ , m ⦂ b)) p q) s)
... | yes p | no ¬p | yes r = yes (n r)
... | yes p | no ¬p | no ¬r = no (λ { s → ¬p refl
                                    ; (n x) → ¬r x })
... | no ¬p | q | yes r = yes (n r)
... | no ¬p | q | no ¬r = no (λ { s → ¬p refl
                                ; (n x) → ¬r x })

dec-∃∈ : (l : String) → (Γ : Context A) → Dec (Σ[ a ∈ A ] l ⦂ a ∈ Γ)
dec-∃∈ l ε = no (λ ())
dec-∃∈ l (Γ , m ⦂ a) with discreteString l m | dec-∃∈ l Γ 
... | yes p | q = yes (a , (transport (cong (λ m → l ⦂ a ∈ (Γ , m ⦂ a)) p) s))
... | no ¬p | yes (b , q) = yes (b , n q)
... | no ¬p | no ¬q = no (λ { (b , s) → ¬p refl
                            ; (b , n r) → ¬q (b , r) })

-- dec-∀∈→ : {B : String → A → Type ℓ} (Γ : Context A) → (∀ l a → Dec (B l a)) → Dec (∀ l a → l ⦂ a ∈ Γ → B l a)
-- dec-∀∈→ {B} ε decB = no (λ x → {!   !})
-- dec-∀∈→ {B} (Γ , l ⦂ a) decB = {!   !}

dec⊎ : Dec A → Dec B → Dec (A ⊎ B)
dec⊎ (yes p) decB = yes (inl p)
dec⊎ (no ¬p) (yes q) = yes (inr q)
dec⊎ (no ¬p) (no ¬q) = no (λ { (inl x) → ¬p x
                             ; (inr x) → ¬q x })

dec→ : Dec A → Dec B → Dec (A → B)
dec→ (yes p) (yes q) = yes (λ _ → q)
dec→ (yes p) (no ¬p) = no (λ f → ¬p (f p))
dec→ (no ¬p) q = yes λ a → ⊥-elim (¬p a)

dec× : Dec A → Dec B → Dec (A × B)
dec× (yes p) (yes q) = yes (p , q)
dec× (yes p) (no ¬q) = no (λ x → ¬q (proj₂ x))
dec× (no ¬p) decB = no (λ x → ¬p (proj₁ x))

tail : Context A → Context A
tail ε = ε
tail (Γ , x ⦂ x₁) = Γ

head : A → Context A → A
head a ε = a
head a (Γ , l ⦂ b) = b

lhead : String → Context A → String
lhead l ε = l
lhead l (Γ , l₁ ⦂ b) = l₁

discreteUnit : Discrete Unit
discreteUnit tt tt = yes refl

discreteContext : Discrete A → Discrete (Context A)
discreteContext discA ε ε = yes refl
discreteContext discA ε (Δ , x ⦂ x₁) = no (λ p → znots (cong length p))
discreteContext discA (Γ , x ⦂ x₁) ε = no (λ p → snotz (cong length p))
discreteContext discA (Γ , l ⦂ a) (Δ , m ⦂ b) with discreteString l m | discA a b | discreteContext discA Γ Δ
... | yes p | yes q | yes r = yes λ i → r i , p i ⦂ q i
... | yes p | yes q | no ¬p = no (λ x → ¬p (cong tail x))
... | yes p | no ¬p | r = no (λ x → ¬p (cong (head a) x))
... | no ¬p | q | r = no (λ x → ¬p (cong (lhead l) x))

AllNodes : Context A → (B : String → A → Type) → Type
AllNodes ε B = Unit
AllNodes (Γ , l ⦂ a) B = AllNodes Γ B × B l a

decAllNodes : {B : String → A → Type} → (∀ l a → Dec (B l a)) → (Γ : Context A) → Dec (AllNodes Γ B)
decAllNodes decB ε = yes tt
decAllNodes decB (Γ , l ⦂ a) = dec× (decAllNodes decB Γ) (decB l a)

filter : {P : String → A → Type} → (∀ l a → Dec (P l a)) → Context A → Context A
filter {P} decP ε = ε
filter {P} decP (Γ , l ⦂ a) with decP l a 
... | yes p = filter decP Γ , l ⦂ a
... | no ¬p = filter decP Γ

mapc : (A → B) → Context A → Context B
mapc f ε = ε
mapc f (Γ , l ⦂ a) = mapc f Γ , l ⦂ f a

filter-AllNodes : ∀ {P} → (decP : ∀ l a → Dec (P l a)) → AllNodes (filter decP Γ) P
filter-AllNodes {Γ = ε} decP = tt
filter-AllNodes {Γ = Γ , l ⦂ a} decP with decP l a 
... | yes p = (filter-AllNodes {Γ = Γ} decP) , p
... | no ¬p = filter-AllNodes {Γ = Γ} decP