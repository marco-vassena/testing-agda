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
 
-- Specific Results chosen based on the outmost quantifier.

data Pass : Set where
  Ok : Pass

-- Property falsifiable for an input
data ¬_for_ {Input : Set} (Property : Set) : Input -> Set where
  CounterExample : (x : Input) -> ¬ Property for x 

data NotFound : Set where

data _by_ {Input : Set} (Property : Set) : Input -> Set where
  Exists : (x : Input) -> Property by x

--------------------------------------------------------------------------------

open import Data.Unit

-- Universe
data U : Set₁ where
  Forall : {A : Set} -> List A -> (p : A -> U) -> U
  Exists : {A : Set} -> List A -> (p : A -> U ) -> U
  Property : (P : Set) -> U

-- Returns the type of the view function required to check if 
-- the given property holds for some input values. 
⟦_⟧ : U -> Set
⟦ Forall {A = A} gen f ⟧ = (a : A) → ⟦ f a ⟧
⟦ Exists {A = A} gen f ⟧ = (a : A) → ⟦ f a ⟧
⟦ Property P ⟧ = Dec P

data Testable : Set₁ where
  C : (u : U) -> (k : ⟦ u ⟧) -> Testable

data Result : Set where
  Yes : Result
  No : Result

-- I guess it does not pass the termination checker because from the type signature of test'
-- it is not visible that the recursive call is structural. 
-- However xs is strictly smaller than x ∷ xs, therefore it terminates. 
-- Having xs as index of U could fix it I think.
test' : (u : U) -> ⟦ u ⟧ -> Result
test' (Forall [] p) check = Yes
test' (Forall (x ∷ xs) p) check with test' (p x) (check x) 
test' (Forall (x ∷ xs) p) check | Yes = test' (Forall xs p) check
test' (Forall (x ∷ xs) p) check | No = No
test' (Exists [] p) check = No
test' (Exists (x ∷ xs) p) check with test' (p x) (check x)
test' (Exists (x ∷ xs) p) check | Yes = Yes
test' (Exists (x ∷ xs) p) check | No = test' (Exists xs p) check
test' (Property P) (yes p) = Yes
test' (Property P) (no ¬p) = No

open import Data.Empty

-- TODO give precise result inspecting the outer quantifier
test : Testable -> Set
test (C u k) with test' u k
test (C u k) | Yes = Pass
test (C u k) | No = ⊥       -- TODO collect input

--------------------------------------------------------------------------------
-- Examples
--------------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality
open import Data.Unit

nats : List ℕ
nats = 0 ∷ 1 ∷ []

lists : List (List ℕ)
lists = ([] ∷ nats ∷ [])

ex0 : U
ex0 = Property Unit

dec-ex0 : ⟦ ex0 ⟧
dec-ex0 = yes unit

test-ex0 : test (C ex0 dec-ex0)
test-ex0 = Ok

ex0' : U
ex0' = Property ⊥

dec-ex0' : ⟦ ex0' ⟧
dec-ex0' = no (λ z → z)

test-ex0' : test (C ex0' dec-ex0')
test-ex0' = {!!}

ex1 : U
ex1 = Forall {ℕ} nats (λ n -> Property (n ≡ n))

dec-ex1 : ⟦ ex1 ⟧
dec-ex1 = λ x -> Data.Nat._≟_ x x

test-ex1 : test (C ex1 dec-ex1) 
test-ex1 = Ok

ex : U
ex =  (Forall {ℕ} nats (λ n -> Exists {List ℕ} lists ( λ xs -> Property (n ≡ (length xs)))))

dec-ex : ⟦ ex ⟧
dec-ex = λ n xs → Data.Nat._≟_ n (length xs)

test-ex : test (C ex dec-ex)
test-ex = {!!}

