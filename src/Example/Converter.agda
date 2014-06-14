module Example.Converter where

open import Converter
open import Base

open import Data.Nat
open import Data.List
open import Reflection


data Even  : ℕ → Set where
  isEven0  : Even 0
  isEven+2 : ∀ {n} → Even n → Even (suc (suc n))

f1 : U (ℕ ∷ [])
f1 = Forall n ~ Property (Even n)

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Sum
open import Data.Product

lemma1 : (n : ℕ) -> Even n
lemma1 = {!!}

lemma2 : (n : ℕ) -> (m : ℕ) -> Even (n + m)
lemma2 = {!!}

lemma3 : (n : ℕ) -> ¬ (Even n)
lemma3 = {!!}

lemma4 : (n : ℕ) -> (Even n) ⊎ (¬ (Even n))
lemma4 = {!!}

lemma5 : ∃ (λ n → Even n)
lemma5 = {!!}

lemma6 : (n : ℕ) -> Even n × (¬ (Even n))
lemma6 = {!!} 

test1 : unquote (convert (quote lemma1)) ≡ (Forall n ~ Property (Even n))
test1 = refl

test2 : unquote (convert (quote lemma2)) ≡ (Forall n ~ Forall m ~ (Property (Even (n + m))))
test2 = refl

test3 : unquote (convert (quote lemma3)) ≡ (Forall n ~ Not (Property (Even n)))
test3 = refl

test4 : unquote (convert (quote lemma4)) ≡ (Forall n ~ (Property (Even n)) ∨ Not (Property (Even n)))
test4 = refl

test5 : unquote (convert (quote lemma5)) ≡ (U.Exists n ~ Property (Even n))
test5 = refl
