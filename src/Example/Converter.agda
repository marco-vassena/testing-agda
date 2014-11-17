-- | This module shows how to use the automatic conversion feature
-- to produce directly a predicate from a lemma under analysis.

{-# OPTIONS --allow-unsolved-metas #-}

module Example.Converter where

open import Test
open import Example.Even

open import Data.Nat
open import Data.List
open import Data.Sum
open import Data.Product using (∃)
open import Reflection
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

--------------------------------------------------------------------------------
-- Example lemmas
-- They are defined as postulates, because the goal is just to show
-- how automatic conversion works.
-- Normally they would contain holes in their definition.
--------------------------------------------------------------------------------

postulate lemma1 : (n : ℕ) -> Even n

postulate lemma2 : (n : ℕ) -> (m : ℕ) -> Even (n + m)

postulate lemma3 : (n : ℕ) -> ¬ (Even n)

postulate lemma4 : (n : ℕ) -> (Even n) ⊎ (¬ (Even n))

postulate lemma5 : Data.Product.∃ (λ n → Even n)

-- | Note that the _×_ instance used in lemma6 is not from the standard library (Data.Product._×_) because
-- that one is defined using the dependent pair Σ, the same used for defining also ∃.
-- With the reflection facilities available at the moment it's not possible to distinguish the two uses,
-- therefore an ad hoc definition of × has been provided and it's recognized by the Converter module. 
postulate lemma6 : (n : ℕ) -> Even n × (¬ (Even n))

postulate lemma7 : Data.Product.∃ (λ n → Data.Product.∃ (λ m → Even (n + m)))

postulate lemma8 : Data.Product.∃ (λ n -> (Even n ⊎ Even (n + 1)))

postulate lemma9 : Data.Product.∃ (λ n -> (m : ℕ) -> (Even n ⊎ Even (n + m)))

postulate lemma10 : Data.Product.∃ (λ n -> ¬ (Even n))

--------------------------------------------------------------------------------
-- Unit tests
--------------------------------------------------------------------------------

test1 : unquote (convert (quote lemma1)) ≡ (Forall n ~ Property (Even n))
test1 = refl

test2 : unquote (convert (quote lemma2)) ≡ (Forall n ~ Forall m ~ (Property (Even (n + m))))
test2 = refl

test3 : unquote (convert (quote lemma3)) ≡ (Forall n ~ Not (Property (Even n)))
test3 = refl

test4 : unquote (convert (quote lemma4)) ≡ (Forall n ~ (Property (Even n)) ∨ Not (Property (Even n)))
test4 = refl

test5 : unquote (convert (quote lemma5)) ≡ (Predicate.Exists n ~ Property (Even n))
test5 = refl

test6 : unquote (convert (quote lemma6)) ≡ (Forall n ~ Property (Even n) ∧ Not (Property (Even n)))
test6 = refl

test7 : unquote (convert (quote lemma7)) ≡ (Predicate.Exists n ~ Predicate.Exists m ~ Property (Even (n + m)))
test7 = refl

test8 : unquote (convert (quote lemma8)) ≡ (Predicate.Exists n ~ (Property (Even n) ∨ Property (Even (n + 1))))
test8 = refl

test9 : unquote (convert (quote lemma9)) ≡ (Predicate.Exists n ~ Predicate.Forall m ~ (Property (Even n) ∨ Property (Even (n + m))))
test9 = refl

test10 : unquote (convert (quote lemma10)) ≡ (Predicate.Exists n ~ Not (Property (Even n)))
test10 = refl
