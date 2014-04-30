module Base where

open import Coinduction
open import Data.Nat
open import Data.Stream
open import Data.List
open import Reflection
open import Relation.Nullary

-- Specifies the options for the test generator. 
-- In principle it depends on the test generator.
Options : Set
Options = ℕ

-- The input of the testcase
Input : Set
Input = ℕ

-- TODO : The constructor must be hidden
data Pass : Set where
  Success : Pass   -- Can contain additional information

data Fail : Set where
  CounterExample : Input -> Fail

-- Checks if P holds a certain finite number of times, drawing the input from the stream.
test : {P : Input -> Set} -> Options -> Stream Input -> ((x : Input) -> Dec (P x)) -> Term
test zero (x ∷ xs) check = quoteTerm Success
test (suc n) (x ∷ xs) check with check x
test (suc n) (x ∷ xs) check | yes p = test n (♭ xs) check
test (suc n) (x ∷ xs) check | no ¬p = quoteTerm (CounterExample x)
