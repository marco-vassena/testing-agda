module Example.Simple where

-- open import Test.Base
-- open import Test.Tester
-- open import Test.Runner

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

trivial : U []
trivial = Property Unit

dec-trivial : ⟦ trivial ⟧
dec-trivial = yes unit

test-trivial : runVerbose (Test trivial on [] by dec-trivial)
test-trivial = Pass (Hold Unit)

impossible : U []
impossible = Property ⊥

dec-impossible : ⟦ impossible ⟧
dec-impossible = no (λ z → z)

test-impossible : runVerbose (Test impossible on [] by dec-impossible)
test-impossible = Failed (DoesNotHold ⊥)

skip-impossible : skip (Test impossible on [] by dec-impossible)
skip-impossible = Skipped

--------------------------------------------------------------------------------
-- Miscellaneous examples
--------------------------------------------------------------------------------

ex1 : U (ℕ ∷ []) 
ex1 = Forall {ℕ} (λ n -> Property (n ≡ n))

dec-ex1 : ⟦ ex1 ⟧
dec-ex1 = λ x -> Data.Nat._≟_ x x

some-nats : List ℕ
some-nats = 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []

lists : List (List ℕ)
lists = [] ∷ (0 ∷ []) ∷ (0 ∷ 1 ∷ []) ∷ (0 ∷ 1 ∷ 2 ∷ []) ∷ []

test-ex1 : run (Test ex1 on [ some-nats ] by dec-ex1) 
test-ex1 = Pass

ex2 : U (ℕ ∷ List ℕ ∷ [])
ex2 =  (Forall (λ n -> Exists {List ℕ} (λ xs -> Property (n ≡ (length xs)))))

dec-ex2 : ⟦ ex2 ⟧
dec-ex2 = λ n xs → Data.Nat._≟_ n (length xs)

test-ex2 : runVerbose (Test ex2 on ((take 2 some-nats) ∷ lists ∷ []) by dec-ex2)
test-ex2 = Pass (Forall ℕ (Exists (zero ∷ []) (Hold (suc zero ≡ suc zero))))
