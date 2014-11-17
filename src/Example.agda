-- | Convenience module that rexports all the examples.

module Example where

-- Basic examples about defining simple properties and tesing them.
open import Example.Simple

-- More realistic examples about natural numbers and eveness.
open import Example.Even

-- Shows the use of the different drivers used to run tests
open import Example.Runner

-- Large collection of examples using all the Predicate combinators. 
open import Example.Combinator

-- Shows how to automatically convert the signature of a lemma in the corresponding Predicate 
open import Example.Converter
