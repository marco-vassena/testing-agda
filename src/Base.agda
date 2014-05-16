{-# OPTIONS --no-termination-check #-}  -- FIX : see test' 

module Base where

open import Coinduction
open import Data.Bool
open import Data.Nat
open import Data.List hiding ( [_] )
open import Reflection
open import Relation.Nullary
open import Function
 
-- Specific Results chosen based on the outmost quantifier.

data Pass : Set where
  Ok : Pass

-- Property falsifiable for an input
data ¬_for_ {Input : Set} (Property : Set) : Input -> Set where
  CounterExample : (x : Input) -> ¬ Property for x 

data NotFound : Set where

data _by_ {Input : Set} (Property : Set) : Input -> Set where
  Exists : (x : Input) -> Property by x

--------------------------------------------------------------------------------

-- Universe
data U : (List Set) -> Set₁ where
  Forall : {A : Set} -> ∀ {xs} -> (p : A -> U xs) -> U (A ∷ xs)
  Exists : {A : Set} -> ∀ {xs} -> (p : A -> U xs) -> U (A ∷ xs)
  Property : (P : Set) -> U []

-- Returns the type of the view function required to check if 
-- the given property holds for some input values. 
⟦_⟧ : ∀ {xs} -> U xs -> Set
⟦ Forall {A = A} f ⟧ = (a : A) → ⟦ f a ⟧
⟦ Exists {A = A} f ⟧ = (a : A) → ⟦ f a ⟧
⟦ Property P ⟧ = Dec P

-- Contains input values for testing a property
data Input (F : Set -> Set) : (List Set) -> Set₁ where
  [] : Input F []
  _∷_ : ∀ {xs} {A : Set} -> F A -> Input F xs -> Input F (A ∷ xs)

infixr 5 _∷_ 

-- Shorthand
[_] : ∀ {F A} -> F A -> Input F (A ∷ [])
[ x ] = x ∷ []

data Testable : Set₁ where
  Test_on_by_ : ∀ {A} -> (u : U A) -> Input List A -> (k : ⟦ u ⟧) -> Testable

data Result : Set where
  Yes : Result
  No : Result

-- I guess it does not pass the termination checker because the Input values 
-- have the same constructors ConsF / ConsE.
-- However xs is strictly smaller than x ∷ xs, therefore it terminates.
-- Maybe use sized types?
test : ∀ {xs} (u : U xs) -> ⟦ u ⟧ -> Input List xs -> Result
test (Forall p) check ([] ∷ input) = Yes
test (Forall p) check ((x ∷ xs) ∷ input) with test (p x) (check x) input
test (Forall p) check ((x ∷ xs) ∷ input) | Yes = test (Forall p) check (xs ∷ input)
test (Forall p) check ((x ∷ xs) ∷ input) | No = No
test (Exists p) check ([] ∷ input) = No
test (Exists p) check ((x ∷ xs) ∷ input) with test (p x) (check x) input 
test (Exists p) check ((x ∷ xs) ∷ input) | Yes = Yes
test (Exists p) check ((x ∷ xs) ∷ input) | No = test (Exists p) check (xs ∷ input)
test (Property P) (yes p) [] = Yes
test (Property P) (no ¬p) [] = No

open import Data.Empty

-- TODO give precise result inspecting the outer quantifier
run : Testable -> Set
run (Test u on input by k) with test u k input
run (Test u on input by k) | Yes = Pass
run (Test u on input by k) | No = ⊥       -- TODO collect input

data Skip : Set where
  Skipped : Skip

-- Used to skip a test
skip : Testable -> Set
skip _ = Skip
