module Base where

open import Coinduction
open import Data.Bool
open import Data.Nat
open import Data.Stream hiding (take)
open import Data.List hiding (take)
open import Data.Vec hiding (take)
open import Data.Product using ( ∃ )
open import Reflection
open import Relation.Nullary
open import Function

data Pass : Set where
  Ok : Pass

data Fail (Input : Set) : Input -> Set where
-- Without constructor it's not possible to fill the hole when a test fail (but still not a compile time error)
--  CounterExample : (x : Input) -> Fail Input x     

data NotFound : Set where

data Found (Input : Set) : Input -> Set where
  Exists : (x : Input) -> Found Input x

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


record ∃Property {Hyp : Set} {Input : Set} : Set₁ where
  constructor Lemma
  field 
    {P} : Input -> Set
    {f} : Hyp -> Input
    dec : Dec' P
    lemma : ∃ (λ h -> P (f h))

-- TODO better names ?

allTrue : {Hyp : Set} {Input : Set} -> List Hyp -> Theorem {Hyp} {Input} -> Set
allTrue [] _ = Pass
allTrue (x ∷ xs) t with (Theorem.dec t) ((Theorem.f t) x)
allTrue (x ∷ xs) t | yes p = allTrue xs t
allTrue (x ∷ xs) t | no ¬p = Fail _ x

-- For existentially qunatified theorems (e.g. ∃ x . P x)
-- FIX : It does not really work with the definition of Theorem, because it encodes with its signature
-- only universally quantified theorems. 
∃True : {Hyp : Set} {Input : Set} -> List Hyp -> ∃Property {Hyp} {Input} -> Set
∃True [] t = NotFound
∃True (x ∷ xs) t with (∃Property.dec t) ((∃Property.f t) x)
∃True (x ∷ xs) t | yes p = Found _ x
∃True (x ∷ xs) t | no ¬p = ∃True xs t
