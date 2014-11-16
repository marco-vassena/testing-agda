-- | This module shows how to use the automatic conversion feature
-- to produce directly a predicate from a lemma under analysis.

module Example.Converter where

open import Test
open import Example.Even

open import Data.Nat
open import Data.List
open import Data.Sum
open import Data.Product
open import Reflection
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

--------------------------------------------------------------------------------
-- Example lemmas
--------------------------------------------------------------------------------

lemma1 : (n : ℕ) -> Even n
lemma1 = {!!}

lemma2 : (n : ℕ) -> (m : ℕ) -> Even (n + m)
lemma2 = {!!}

lemma3 : (n : ℕ) -> ¬ (Even n)
lemma3 = {!!}

lemma4 : (n : ℕ) -> (Even n) ⊎ (¬ (Even n))
lemma4 = {!!}

lemma5 : Data.Product.∃ (λ n → Even n)
lemma5 = {!!}

lemma6 : (n : ℕ) -> Even n × (¬ (Even n))
lemma6 = {!!}

lemma7 : Data.Product.∃ (λ n → Data.Product.∃ (λ m → Even (n + m)))
lemma7 = {!!}

lemma8 : Data.Product.∃ (λ n -> (Even n ⊎ Even (n + 1)))
lemma8 = {!!}

lemma9 : Data.Product.∃ (λ n -> (m : ℕ) -> (Even n ⊎ Even (n + m)))
lemma9 = {!!}

open import Function

lemma10 : Data.Product.∃ (λ n -> ¬ (Even n))
lemma10 = {!!}

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

-- TODO add special construct for ×
test6 : {!!} -- unquote (convert (quote lemma6)) ≡ (Forall n ~ Property (Even n) ∧ Not (Property (Even n)))
test6 = {!!}

test7 : unquote (convert (quote lemma7)) ≡ (Predicate.Exists n ~ Predicate.Exists m ~ Property (Even (n + m)))
test7 = refl

test8 : unquote (convert (quote lemma8)) ≡ (Predicate.Exists n ~ (Property (Even n) ∨ Property (Even (n + 1))))
test8 = refl

test9 : unquote (convert (quote lemma9)) ≡ (Predicate.Exists n ~ Predicate.Forall m ~ (Property (Even n) ∨ Property (Even (n + m))))
test9 = refl

test10 : unquote (convert (quote lemma10)) ≡ (Predicate.Exists n ~ Not (Property (Even n)))
test10 = refl
