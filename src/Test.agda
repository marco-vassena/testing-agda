module Test where

-- Predicate data type
open import Test.Base public

-- Drivers to 'run' test cases
open import Test.Runner public

-- Testing framework
open import Test.Tester public

-- Result data type
open import Test.Result public

-- Automatic conversion to predicates 
open import Test.Converter public

-- Input data type
open import Test.Input public
