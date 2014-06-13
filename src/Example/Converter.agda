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

-- quoteTerm f1
-- con Base.U.Forall
-- (arg hidden relevant (def Data.Nat.ℕ []) ∷
--  arg hidden relevant (con Base.BListTree.[] []) ∷
--  arg visible relevant
--  (lam visible
--   (con Base.U.Property
--    (arg visible relevant
--     (def Converter.Even (arg visible relevant (var 0 []) ∷ []))
--     ∷ [])))
--  ∷ [])

-- What I want (the signature of lemma) can be retrieved using 
--     type (quote lemma)
-- which produces 
-- el (lit 0)
-- (pi
--  (arg visible relevant
--   (el (lit 0) (def Data.Nat.ℕ .Data.List.List.[])))
--  (el (lit 0)
--   (def Converter.Even
--    (arg visible relevant (var 0 .Data.List.List.[]) .Data.List.List.∷
--     .Data.List.List.[]))))

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

-- el (lit 0)
-- (pi (arg visible relevant (el (lit 0) (def Data.Nat.ℕ [])))
--  (el (lit 0)
--   (def Relation.Nullary.Core.¬_
--    (arg hidden relevant unknown ∷
--     arg visible relevant
--     (def Example.Converter.Even (arg visible relevant (var 0 []) ∷ []))
--     ∷ []))))

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
