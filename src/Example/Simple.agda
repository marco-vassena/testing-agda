module Example.Simple where

open import Test

open import Data.List hiding ([_])
open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ( [_] )

--------------------------------------------------------------------------------
-- Constant properties
--------------------------------------------------------------------------------

-- It always holds
trivial : Predicate []
trivial = Property Unit

dec-trivial : ⟦ trivial ⟧
dec-trivial = yes unit

-- The test succeeds
test-trivial : runVerbose (Test trivial on [] by dec-trivial)
test-trivial = Pass (Hold Unit)

-- It never holds
impossible : Predicate []
impossible = Property ⊥

dec-impossible : ⟦ impossible ⟧
dec-impossible = no (λ z → z)

-- Running the test shows a failure
test-impossible : runVerbose (Test impossible on [] by dec-impossible)
test-impossible = Failed (DoesNotHold ⊥)

skip-impossible : skip (Test impossible on [] by dec-impossible)
skip-impossible = Skipped

--------------------------------------------------------------------------------
-- Miscellaneous examples
--------------------------------------------------------------------------------

ex1 : Predicate (ℕ ∷ []) 
ex1 = Forall {ℕ} (λ n -> Property (n ≡ n))

-- ex1 using the pretty syntax
pretty-ex1 : Predicate (ℕ ∷ [])
pretty-ex1 = Forall n ~ (Property (n ≡ n))

dec-ex1 : ⟦ ex1 ⟧
dec-ex1 = λ x -> Data.Nat._≟_ x x

some-nats : List ℕ
some-nats = 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []

lists : List (List ℕ)
lists = [] ∷ (0 ∷ []) ∷ (0 ∷ 1 ∷ []) ∷ (0 ∷ 1 ∷ 2 ∷ []) ∷ []

test-ex1 : run (Test ex1 on [ some-nats ] by dec-ex1) 
test-ex1 = Pass

--------------------------------------------------------------------------------

ex2 : Predicate (ℕ ∷ List ℕ ∷ [])
ex2 =  (Forall (λ n -> Exists {List ℕ} (λ xs -> Property (n ≡ (length xs)))))

pretty-ex2 : Predicate (ℕ ∷ List ℕ ∷ [])
pretty-ex2 =  Forall n ~ Exists xs ~ (Property (n ≡ (length xs)))

dec-ex2 : ⟦ ex2 ⟧
dec-ex2 = λ n xs → Data.Nat._≟_ n (length xs)

test-ex2 : runVerbose (Test ex2 on ((take 2 some-nats) ∷ lists ∷ []) by dec-ex2)
test-ex2 = Pass (ForAll ℕ (∃ < List ℕ > ✓))
