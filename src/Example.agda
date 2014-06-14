module Example where

open import Test.Base
open import Test.Runner
open import Test.Tester hiding (Test_on_by_)
open import Test.StreamGenerator

open import Data.Nat
open import Data.Product as P hiding ( ∃ )
open import Data.List hiding (take ; [_] )
open import Relation.Binary.PropositionalEquality hiding ( [_] )
open import Relation.Nullary

open import Example.Simple
open import Example.Even
open import Example.Runner
open import Example.Combinator
-- TODO import also Example.Converter
