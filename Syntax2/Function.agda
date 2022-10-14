--------------------------------------------------------------------------------
-- A function consists of an entry block and a sequence of basic blocks
-- Entry blocks have no predecessors (and thus no phi nodes)
--------------------------------------------------------------------------------

{-# OPTIONS --cubical #-}

module Syntax2.Function where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Data.Prod
open import Cubical.Data.Sum
open import Cubical.Data.Bool
open import Cubical.Data.Unit
open import Agda.Builtin.String
open import Cubical.HITs.ListedFiniteSet
open import Cubical.HITs.PropositionalTruncation renaming (rec to prec)
open import Cubical.Data.Empty renaming (rec to ⊥-elim)
open import Cubical.Relation.Nullary

open import Syntax2.Type
open import Syntax2.Context
open import Syntax2.Block
open import Syntax2.Value
open import Syntax2.Instruction

record Edges : Type where
  constructor edges
  field
    ins : Context Unit
    outs : Context Unit 

discreteEdges : Discrete Edges
discreteEdges (edges ins outs) (edges ins' outs') with discreteContext discreteUnit ins ins' | discreteContext discreteUnit outs outs'
... | yes p | yes q = yes (λ i → edges (p i) (q i))
... | yes p | no ¬p = no (λ x → ¬p (cong Edges.outs x))
... | no ¬p | q = no (λ x → ¬p (cong Edges.ins x))

private
  variable
    A B C : Typ
    Γ : Context Typ
    Γⁱⁿ Γᵒᵘᵗ : Context Unit
    Δ' : Context (Context Typ)
    Ω' : Context Edges

infixl 6 begin_⦂⦂_
infixl 5 _;_⦂⦂_

data PreFunction (A : Typ) (Γᵖ : Context Typ) (Δ : Context (Context Typ)) (Ω : Context Edges) : 
  Context (Context Typ) → Context Edges → Type where

  begin_⦂⦂_ : (l : String) 
              → PreBlock l Γᵖ Δ A ε Γᵒᵘᵗ Γ 
              → PreFunction A Γᵖ Δ Ω (ε , l ⦂ Γ) (ε , l ⦂ edges ε Γᵒᵘᵗ)
  _;_⦂⦂_ : PreFunction A Γᵖ Δ Ω Δ' Ω' → (l : String) → PreBlock l Γᵖ Δ A Γⁱⁿ Γᵒᵘᵗ Γ → PreFunction A Γᵖ Δ Ω (Δ' , l ⦂ Γ) (Ω' , l ⦂ edges Γⁱⁿ Γᵒᵘᵗ)

record Function (A : Typ) (Γᵖ : Context Typ) : Type where
  -- constructor function
  field
    {Δ} : Context (Context Typ)
    {Ω} : Context Edges
    function : PreFunction A Γᵖ Δ Ω Δ Ω
    in→out : AllNodes Ω (λ l (edges lⁱ lᵒ) → AllNodes Ω (λ m (edges mⁱ mᵒ) → l ⦂ tt ∈ mⁱ → m ⦂ tt ∈ lᵒ))
    out→in : AllNodes Ω (λ l (edges lⁱ lᵒ) → AllNodes Ω (λ m (edges mⁱ mᵒ) → m ⦂ tt ∈ lᵒ → l ⦂ tt ∈ mⁱ))
    -- in→out : ∀ {l m lⁱ lᵒ mⁱ mᵒ} → l ⦂ edges lⁱ lᵒ ∈ Ω → m ⦂ edges mⁱ mᵒ ∈ Ω → l ⦂ tt ∈ mⁱ → m ⦂ tt ∈ lᵒ
    -- out→in : ∀ {l m lⁱ lᵒ mⁱ mᵒ} → l ⦂ edges lⁱ lᵒ ∈ Ω → m ⦂ edges mⁱ mᵒ ∈ Ω → m ⦂ tt ∈ lᵒ → l ⦂ tt ∈ mⁱ

autofunc : ∀ {Δ Ω Γᵖ} 
         → PreFunction A Γᵖ Δ Ω Δ Ω 
         → {True (decAllNodes (λ l (edges lⁱ lᵒ) → decAllNodes (λ m (edges mⁱ mᵒ) → dec→ (dec-∈ discreteUnit l tt mⁱ) (dec-∈ discreteUnit m tt lᵒ)) Ω) Ω)}
         → {True (decAllNodes (λ l (edges lⁱ lᵒ) → decAllNodes (λ m (edges mⁱ mᵒ) → dec→ (dec-∈ discreteUnit m tt lᵒ) (dec-∈ discreteUnit l tt mⁱ)) Ω) Ω)}
         → Function A Γᵖ
Function.Δ (autofunc f {p}) = _
Function.Ω (autofunc f {p}) = _
Function.function (autofunc f {p}) = f
Function.in→out (autofunc f {p}) = toWitness p
Function.out→in (autofunc f {p} {q}) = toWitness q

min : Function int (ε , "x" ⦂ int , "y" ⦂ int)
min = autofunc (begin 
  "entry" ⦂⦂ ((                                preds ε ;;) ; 
    "cond" ≔ lte (% "x") (% "y")) ;; 
    brc (% "cond") (%b "ry") (%b "rx") ;
  "rx" ⦂⦂ (                                    preds (ε , "entry" ⦂ tt) ;;) ;; 
    ret int (% "x") ;
  "ry" ⦂⦂ (                                    preds (ε , "entry" ⦂ tt) ;;) ;; 
    ret int (% "y"))



-- Function.Δ min = _
-- Function.Ω min = _
-- Function.function min = begin 
--   "entry" ⦂⦂ ((preds ε ;;) ; 
--     "cond" ≔ lte (% "x") (% "y")) ;; 
--     brc (% "cond") (%b "rx") (%b "ry") ;
--   "rx" ⦂⦂ (preds (ε , "entry" ⦂ tt) ;;) ;; 
--     ret int (% "x") ;
--   "ry" ⦂⦂ (preds (ε , "entry" ⦂ tt) ;;) ;; 
--     ret int (% "y")
-- Function.in→out min = 
--   λ { s s (n ())
--     ; s (n s) (n ())
--     ; s (n (n s)) ()
--     ; s (n (n (n ()))) l∈m
--     ; (n s) s (n ())
--     ; (n s) (n s) (n ())
--     ; (n s) (n (n s)) ()
--     ; (n s) (n (n (n ()))) l∈m
--     ; (n (n s)) s l∈m → s
--     ; (n (n s)) (n s) l∈m → n s
--     ; (n (n s)) (n (n s)) ()
--     ; (n (n s)) (n (n (n ()))) l∈m 
--     }
-- Function.out→in min = 
--    λ { (n (n s)) s m∈l → s
--      ; (n (n s)) (n s) m∈l → s
--      ; (n (n s)) (n (n s)) (n (n ())) }

     
-- min = function (( begin 
--   "entry" ⦂⦂ 
--     (((blockstart ε ;;) ; 
--     "cond" ≔ lte (param "x" (n s)) (param "y" s)) ;; 
--     brc (label "cond" s) ("rx" , n s) ("ry" , s))
--     ) ;
--   "rx" ⦂⦂
--     ((blockstart (ε , "entry" ⦂ tt) ;;) ;; ret int (param "x" (n s))) ;
--   "ry" ⦂⦂
--     ((blockstart (ε , "entry" ⦂ tt) ;;) ;; ret int (param "y" s)))
--   (λ { s s (n ())
--      ; s (n s) (n ())
--      ; s (n (n s)) ()
--      ; s (n (n (n ()))) l∈m
--      ; (n s) s (n ())
--      ; (n s) (n s) (n ())
--      ; (n s) (n (n s)) ()
--      ; (n s) (n (n (n ()))) l∈m
--      ; (n (n s)) s l∈m → s
--      ; (n (n s)) (n s) l∈m → n s
--      ; (n (n s)) (n (n s)) ()
--      ; (n (n s)) (n (n (n ()))) l∈m })
  -- λ { (n (n s)) s m∈l → s
  --   ; (n (n s)) (n s) m∈l → s
  --   ; (n (n s)) (n (n s)) (n (n ())) }


-- infix 5 entry_≔_
-- infixl 4 _;_≔_



-- data PreFunction (Γᵖ : Context Typ) (Δ : Context BlockContext) (A : Typ) : Context BlockContext → Type where
--   -- entry block can't have predecessors
--   -- no predecessors -> no phi nodes
--   -- TODO: currently, no nice way to constrain the predecessors, Γᵉ are the outgoing edges
--   entry_≔_ : (l : String) → BlockBody l Δ Γᵖ Γ A ε Γᵉ → PreFunction Γᵖ Δ A (ε , l ⦂ blk A Γᵉ Γ)
--                                                                              -- ^ we need to be able to reference the entry block in phi nodes,
--                                                                              --   but not be able to branch to it (which this doesn't do)
--   _;_≔_ : PreFunction Γᵖ Δ A Δ' → (l : String) → Block l Δ Γᵖ Γ A Γᵉ → PreFunction Γᵖ Δ A (Δ' , l ⦂ blk A Γᵉ Γ)


--   -- _≔_;_ : (l : String) → Block l Δ Γᵖ Γ A Γᵉ → PreFunction Γᵖ Δ A Δ' → PreFunction Γᵖ Δ A (Δ' , l ⦂ blk A Γᵉ Γ)
--   -- _≔_fin : (l : String) → Block l Δ Γᵖ Γ A Γᵉ → PreFunction Γᵖ Δ A (ε , l ⦂ blk A Γᵉ Γ)

-- record Function (Γᴾ : Context Typ) (A : Typ) : Type where
--   constructor func
--   field
--     {Δ} : Context BlockContext -- Δ contains all the "self-refererential" data we need in each block
--                                   -- Type of return
--                                   -- Context of labels in block
--                                   -- Outgoing edges
--                                -- This never needs to be written implicitly since it will always be 
--                                -- unified with the inductivly defined analog at all levels, e.g.
--                                -- We inductivly build up the context of labels in a block, and the
--                                -- base case for a block (the terminator) ensures that this unifys 
--                                -- with the block context (or rather an index which will become part
--                                -- of the block context
--     func : PreFunction Γᴾ Δ A Δ

  