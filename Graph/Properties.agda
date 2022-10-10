{-# OPTIONS --cubical #-}

module Graph.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.ListedFiniteSet
open import Cubical.Data.Prod
open import Graph.Base
import Graph.Sets.Base as Sets
import Util.LFSet.Properties as LFSet

private
  variable
    ℓ : Level
    A : Type ℓ
    x y z : Graph A

+-pre-idemp : x + x + ε ≡ x
+-pre-idemp {x = x} = 
  x + x + ε              ≡⟨ (λ i → ⇒-identʳ {x = x} (~ i) + ⇒-identʳ {x = x} (~ i) + ⇒-identʳ {x = ε} (~ i)) ⟩
  x ⇒ ε + x ⇒ ε + ε ⇒ ε  ≡⟨ sym ⇒-decomp ⟩
  x ⇒ ε ⇒ ε              ≡⟨ ⇒-identʳ ⟩
  x ⇒ ε                  ≡⟨ ⇒-identʳ ⟩
  x                      ∎

+-identʳ : x + ε ≡ x
+-identʳ {x = x} = 
  x + ε                  ≡⟨ sym +-pre-idemp ⟩
  x + ε + (x + ε) + ε    ≡⟨ cong (_+ ε) (sym +-assoc) ⟩  
  x + ε + x + ε + ε      ≡⟨ cong (λ a → a + ε + ε) +-comm ⟩  
  x + (x + ε) + ε + ε    ≡⟨ cong (λ a → a + ε + ε) (sym +-assoc) ⟩  
  x + x + ε + ε + ε      ≡⟨ cong (_+ ε) +-assoc ⟩  
  x + x + (ε + ε) + ε    ≡⟨ +-assoc ⟩  
  x + x + (ε + ε + ε)    ≡⟨ cong (x + x +_) +-pre-idemp ⟩  
  x + x + ε              ≡⟨ +-pre-idemp ⟩  
  x                      ∎

+-idemp : x + x ≡ x
+-idemp {x = x} = 
  x + x        ≡⟨ cong (x +_) (sym +-identʳ) ⟩ 
  x + (x + ε)  ≡⟨ sym +-assoc ⟩ 
  x + x + ε    ≡⟨ +-pre-idemp ⟩
  x            ∎

⇒-sat : x ⇒ x ⇒ x ≡ x ⇒ x
⇒-sat {x = x} =
  x ⇒ x ⇒ x              ≡⟨ ⇒-decomp ⟩  
  x ⇒ x + x ⇒ x + x ⇒ x  ≡⟨ cong (_+ x ⇒ x) +-idemp ⟩  
  x ⇒ x + x ⇒ x          ≡⟨ +-idemp ⟩  
  x ⇒ x                  ∎

⇒-absorb-+ : x ⇒ y + x + y ≡ x ⇒ y
⇒-absorb-+ {x = x} {y = y} =
  x ⇒ y + x + y          ≡⟨ cong (λ a → x ⇒ y + a + y) (sym ⇒-identʳ) ⟩
  x ⇒ y + x ⇒ ε + y      ≡⟨ cong (x ⇒ y + x ⇒ ε +_) (sym ⇒-identʳ) ⟩
  x ⇒ y + x ⇒ ε + y ⇒ ε  ≡⟨ sym ⇒-decomp ⟩
  x ⇒ y ⇒ ε              ≡⟨ ⇒-identʳ ⟩
  x ⇒ y                  ∎

fromNodes : LFSet A → Graph A
fromNodes [] = ε
fromNodes (x ∷ xs) = node x + fromNodes xs
fromNodes (dup x xs i) = (sym (+-assoc {x = node x} {y = node x}) ∙ cong (_+ fromNodes xs) +-idemp) i
fromNodes (comm x y xs i) = (sym (+-assoc {x = node x} {y = node y}) ∙ cong (_+ fromNodes xs) +-comm ∙ +-assoc) i
fromNodes (trunc xs ys p q i j) = trunc (fromNodes xs) (fromNodes ys) (cong fromNodes p) (cong fromNodes q) i j

fromEdges : LFSet (A × A) → Graph A
fromEdges [] = ε
fromEdges ((x , y) ∷ xs) = node x ⇒ node y + fromEdges xs
fromEdges (dup x xs i) = {!   !}
fromEdges (comm x y xs i) = {!   !}
fromEdges (trunc xs xs₁ x y i i₁) = {!   !}

toSets : Graph A → Sets.Graph A
toSets ε = [] Sets., []
toSets (node x) = (x ∷ []) Sets., []
toSets (x + y) = Sets.overlay (toSets x) (toSets y)
toSets (x ⇒ y) = Sets.connect (toSets x) (toSets y)
toSets (+-comm {x = x} {y} i) = Sets.overlay-comm (toSets x) (toSets y) i
toSets (+-assoc i) = {!   !}
toSets (⇒-identˡ i) = {! toSets x  !}
toSets (⇒-identʳ {x = x} i) = {! toSets x  !}
toSets (⇒-assoc i) = {!   !}
toSets (⇒-dist-+ i) = {!   !}
toSets (+-dist-⇒ i) = {!   !}
toSets (⇒-decomp i) = {!   !}
toSets (trunc x y p q i j) = Sets.isSetGraph (toSets x) (toSets y) (cong toSets p) (cong toSets q) i j

fromSets : Sets.Graph A → Graph A
fromSets (nodes Sets., edges) = fromNodes nodes + fromEdges edges

toSets-fromNodes : ∀ (xs : LFSet A) → toSets (fromNodes xs) ≡ xs Sets., []
toSets-fromNodes = PropElim.f refl (λ { x {xs} p → 
  Sets.overlay ((x ∷ []) Sets., []) (toSets (fromNodes xs))  ≡⟨ cong (Sets.overlay ((x ∷ []) Sets., [])) p ⟩
  Sets.overlay ((x ∷ []) Sets., []) (xs Sets., [])           ≡⟨ refl ⟩
  ((x ∷ xs) Sets., [])                                       ∎
  }) (λ _ → Sets.isSetGraph _ _)

toSets-fromEdges : ∀ (xs : LFSet (A × A)) → toSets (fromEdges xs) ≡ LFSet.unpair xs Sets., xs
toSets-fromEdges = PropElim.f refl (λ { (x , y) {xs} p → 
  cong₂ Sets._,_ (cong (λ a → x ∷ y ∷ a) (cong Sets.Graph.nodes p)) 
                 (cong ((x , y) ∷_) (cong Sets.Graph.edges p)) 
                 }) 
  (λ _ → Sets.isSetGraph _ _)

setsIso : Iso (Graph A) (Sets.Graph A)
Iso.fun setsIso x = toSets x
Iso.inv setsIso x = fromSets x
Iso.rightInv setsIso = lemma
  where
  lemma : ∀ (x : Sets.Graph A) → toSets (fromSets x) ≡ x
  lemma (nodes Sets., edges) = 
    Sets.overlay (toSets (fromNodes nodes)) (toSets (fromEdges edges))  ≡⟨ cong₂ Sets.overlay (toSets-fromNodes nodes) (toSets-fromEdges edges) ⟩ 
    Sets.overlay (nodes Sets., []) (LFSet.unpair edges Sets., edges)    ≡⟨ {!   !} ⟩ 
    (nodes ++ []) Sets., edges                                          ≡⟨ cong (Sets._, edges) (LFSet.++-identʳ nodes) ⟩ 
    nodes Sets., edges                                                  ∎
Iso.leftInv setsIso = {!   !} 