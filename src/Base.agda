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

-- Universe
data U : (List Set) -> Set₁ where
  Forall : {A : Set} -> ∀ {xs} -> (p : A -> U xs) -> U (A ∷ xs)
  Exists : {A : Set} -> ∀ {xs} -> (p : A -> U xs) -> U (A ∷ xs)
  Property : (P : Set) -> U []

⟦_⟧ : ∀ {xs} -> U xs -> Set
⟦_⟧ (Forall {A = A} f) = (a : A) → ⟦ f a ⟧
⟦ Exists {A = A} f ⟧ = (a : A) → ⟦ f a ⟧
⟦ Property P ⟧ = Dec P

-- Contains input values for testing a property
data Input : ∀ xs -> U xs -> Set₁ where
  Nil : ∀ {u} -> Input [] u 
  ConsF : ∀ {xs} {A : Set} {u : U xs} -> List A -> Input xs u -> Input (A ∷ xs) (Forall (λ x → u)) 
  ConsE : ∀ {xs} {A : Set} {u : U xs} -> List A -> Input xs u -> Input (A ∷ xs) (Exists (λ x → u)) 

data Testable : Set₁ where
  C : ∀ {A} -> (u : U A) -> (k : ⟦ u ⟧) -> Input A u -> Testable

data Result : Set where
  Yes : Result
  No : Result

-- I guess it does not pass the termination checker because the Input values 
-- have the same constructors ConsF / ConsE.
-- However xs is strictly smaller than x ∷ xs, therefore it terminates. 
test' : ∀ {xs} (u : U xs) -> ⟦ u ⟧ -> Input xs u  -> Result
test' (Forall ._) check (ConsF [] gen) = Yes
test' (Forall ._) check (ConsF {u = u} (x ∷ xs) gen) with test' u (check x) gen
test' (Forall ._) check (ConsF (x ∷ xs) gen) | Yes = test' (Forall _) check (ConsF xs gen)
test' (Forall ._) check (ConsF (x ∷ xs) gen) | No = No
test' (Exists ._) check (ConsE {u = u} [] gen) = No
test' (Exists ._) check (ConsE {u = u} (x ∷ xs) gen) with test' u (check x) gen
test' (Exists ._) check (ConsE (x ∷ xs) gen) | Yes = Yes
test' (Exists ._) check (ConsE (x ∷ xs) gen) | No = test' (Exists _) check (ConsE xs gen)
test' (Property P) (yes p) Nil = Yes
test' (Property P) (no ¬p) Nil = No

open import Data.Empty

test : Testable -> Set
test (C u k input) with test' u k input
test (C u k input) | Yes = Pass
test (C u k input) | No = ⊥       -- TODO collect input

--------------------------------------------------------------------------------
-- Examples
--------------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality
open import Data.Unit

nats : List ℕ
nats = 0 ∷ 1 ∷ []

lists : List (List ℕ)
lists = ([] ∷ nats ∷ [])

ex0 : U []
ex0 = Property Unit

dec-ex0 : ⟦ ex0 ⟧
dec-ex0 = yes unit

test-ex0 : test (C ex0 dec-ex0 Nil)
test-ex0 = Ok

ex1 : U (ℕ ∷ []) 
ex1 = Forall {ℕ} (λ n -> Property (n ≡ n))

dec-ex1 : ⟦ ex1 ⟧
dec-ex1 = λ x -> Data.Nat._≟_ x x

test-ex1 : test (C ex1 dec-ex1 {!ConsF nats Nil!}) 
test-ex1 = {!!}

ex : U (ℕ ∷ List ℕ ∷ [])
ex =  (Forall {ℕ} (λ n -> Exists {List ℕ} ( λ xs -> Property (n ≡ (length xs)))))

dec-ex : ⟦ ex ⟧
dec-ex = λ n xs → Data.Nat._≟_ n (length xs)

test-ex : test (C ex dec-ex {!ConsF nats (ConsE lists Nil) !})
test-ex = {!!}

