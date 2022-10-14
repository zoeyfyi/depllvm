{-# OPTIONS --cubical #-}

module Util.String.Base where

open import Agda.Builtin.String public 
open import Agda.Builtin.Char public

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Relation.Nullary
open import Cubical.Data.Nat
open import Cubical.Data.List

charToℕ : Char → ℕ
charToℕ = primCharToNat

ℕToChar : ℕ → Char
ℕToChar = primNatToChar

postulate ℕCharSection : section ℕToChar charToℕ

discreteChar : Discrete Char
discreteChar = sectionDiscrete ℕToChar charToℕ ℕCharSection discreteℕ

chars : String → List Char
chars = primStringToList

string : List Char → String
string = primStringFromList

postulate stringSection : section string chars

discreteString : Discrete String
discreteString = sectionDiscrete string chars stringSection (discreteList discreteChar)