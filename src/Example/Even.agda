-- Examples with Even property

module Example.Even where

open import Test hiding (Test_on_by_)
open import Test.Input.Stream

open import Coinduction
open import Data.Nat
open import Data.Stream
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ( [_] )

-- Input stream, all the natural numbers
nats : Stream ℕ
nats = go 0
  where 
    go : ℕ -> Stream ℕ
    go n = n ∷ ♯ (go (n + 1))

data Even  : ℕ → Set where
  isEven0  : Even 0
  isEven+2 : ∀ {n} → Even n → Even (suc (suc n))

-- Even is a decidable property.
isEven? : (n : ℕ) -> Dec (Even n)
isEven? zero = yes isEven0
isEven? (suc zero) = no (λ ())
isEven? (suc (suc n)) with isEven? n
isEven? (suc (suc n)) | yes p = yes (isEven+2 p)
isEven? (suc (suc n)) | no ¬p = no ( \ p -> ¬p (unpack p) )
  where unpack : ∀ {n} -> Even (suc (suc n)) -> Even n
        unpack (isEven+2 r) = r

--------------------------------------------------------------------------------
-- Even properties
--------------------------------------------------------------------------------

test-even-double : run (Test Forall (λ n → Property (Even (n + n))) on [ nats ] by (λ n → isEven? (n + n)))
test-even-double = Pass

test-all-even : runVerbose (Test (Forall (λ n → Property (Even n))) on [ nats ] by isEven?)
test-all-even = Failed (∃ ⟨ 1 ⟩ (DoesNotHold (Even 1)))

test-all-even-evens : run (Test Forall (λ n → Property (Even n)) on  [ evens nats ] by isEven?)
test-all-even-evens = Pass

test-some-even : runVerbose (Test Exists (λ n → Property (Even n)) on [ nats ] by isEven?)
test-some-even = Pass (∃ ⟨ 0 ⟩ (Hold (Even 0)))

test-some-even-odds : run (Test (Exists (λ n → Property (Even n))) on [ odds nats ] by isEven?)
test-some-even-odds = Failed

-- The order of the quantifiers is relevant:
-- For some fixed n, does it hold for all m that Even (n + m) ?
test-idem : runVerbose (Test Exists (λ n → Forall (λ m -> Property (Even (n + m)))) 
                       on nats ∷ (nats ∷ [])
                       by (λ n m → isEven? (n + m)))
test-idem = Failed (¬∃ ℕ (∃ < ℕ > ✗))

-- Changing the order instead the property holds.
-- For all n, m can be found such that Even (n + m)
test-idem2 : runVerbose (Test Forall n ~ Exists m ~ Property (Even (n + m)) 
                        on nats ∷ (nats ∷ []) 
                        by (λ n m → isEven? (n + m)))
test-idem2 = Pass (ForAll ℕ (∃ < ℕ > ✓))
