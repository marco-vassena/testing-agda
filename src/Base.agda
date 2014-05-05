module Base where

open import Coinduction
open import Data.Bool
open import Data.Nat
open import Data.Stream hiding (take)
open import Data.List hiding (take)
open import Data.Vec hiding (take)
open import Reflection
open import Relation.Nullary
open import Function

-- Specifies the options for the test generator. 
-- In principle they depend on the test generator.
-- At the moment is just the number of test cases generated.
Options : Set
Options = ℕ

data Pass : Set where
  Ok : Pass

data Fail (Input : Set) : Input -> Set where
  CounterExample : (x : Input) -> Fail Input x

-- Combinators

take : ∀ {a} -> ℕ -> Stream a -> List a
take {a} n = toList ∘ (Data.Stream.take {a} n)

Dec' : {Input : Set} -> (P : Input -> Set) -> Set
Dec' {Input} P = (x : Input) -> Dec (P x)

record Theorem {Hyp : Set} {Input : Set} : Set₁ where
  constructor Lemma
  field 
    {P} : Input -> Set
    {f} : Hyp -> Input
    dec : Dec' P
    lemma : (h : Hyp) -> P (f h)

allTrue : {Hyp : Set} {Input : Set} -> List Hyp -> Theorem {Hyp} {Input} -> Set
allTrue [] _ = Pass
allTrue (x ∷ xs) t with (Theorem.dec t) ((Theorem.f t) x)
allTrue (x ∷ xs) t | yes p = allTrue xs t
allTrue (x ∷ xs) t | no ¬p = Fail _ x
