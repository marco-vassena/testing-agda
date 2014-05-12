module Base where

open import Coinduction
open import Data.Bool
open import Data.Nat
open import Data.Stream hiding (take)
open import Data.List hiding (take)
open import Data.Vec hiding (take)
open import Data.Product as P hiding ( ∃ )
open import Reflection
open import Relation.Nullary
open import Function

take : ∀ {a} -> ℕ -> Stream a -> List a
take {a} n = toList ∘ (Data.Stream.take {a} n)

-- Dependent types predicate decidability
Dec' : {Input : Set} -> (P : Input -> Set) -> Set
Dec' {Input} P = (x : Input) -> Dec (P x)

--------------------------------------------------------------------------------
-- ∀-Properties
--------------------------------------------------------------------------------

-- Possible results
data Pass : Set where
  Ok : Pass

data Fail (Input : Set) : Input -> Set where
  CounterExample : (x : Input) -> Fail Input x

record ∀Property {Hyp : Set} {Input : Set} : Set₁ where
  constructor Lemma
  field 
    {P} : Input -> Set
    {f} : Hyp -> Input
    dec : Dec' P
    lemma : (h : Hyp) -> P (f h)

forAll : {Hyp : Set} {Input : Set} -> List Hyp -> ∀Property {Hyp} {Input} -> Set
forAll [] _ = Pass
forAll (x ∷ xs) t with (∀Property.dec t) ((∀Property.f t) x)
forAll (x ∷ xs) t | yes p = forAll xs t
forAll (x ∷ xs) t | no ¬p = Fail _ x

--------------------------------------------------------------------------------
-- ∃Property
--------------------------------------------------------------------------------

-- Results
data NotFound : Set where

data Found (Input : Set) : Input -> Set where
  Exists : (x : Input) -> Found Input x

record ∃Property {Hyp : Set} {Input : Set} : Set₁ where
  constructor Lemma
  field 
    {P} : Input -> Set
    {f} : Hyp -> Input
    dec : Dec' P
    lemma : P.∃ (λ h -> P (f h))

-- For existentially qunatified theorems (e.g. ∃ x . P x)
∃ : {Hyp : Set} {Input : Set} -> List Hyp -> ∃Property {Hyp} {Input} -> Set
∃ [] t = NotFound
∃ (x ∷ xs) t with (∃Property.dec t) ((∃Property.f t) x)
∃ (x ∷ xs) t | yes p = Found _ x
∃ (x ∷ xs) t | no ¬p = ∃ xs t
