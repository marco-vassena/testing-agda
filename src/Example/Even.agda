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

-- Even n is the proof that n is even
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

doubleEven : Predicate (ℕ ∷ [])
doubleEven = Forall n ~ Property (Even (n + n))

isDoubleEven? : ⟦ doubleEven ⟧
isDoubleEven? n = isEven? (n + n)

test-doubleEven : run (Test doubleEven on [ nats ] by isDoubleEven?)
test-doubleEven = Pass

allEven : Predicate (ℕ ∷ [])
allEven = Forall n ~ Property (Even n) 

test-allEven : runVerbose (Test allEven on [ nats ] by isEven?)
test-allEven = Failed (∃ ⟨ 1 ⟩ (DoesNotHold (Even 1)))

-- `Testing shows the presence, not the absence of bugs'
-- The same property (∀ n . Even n) pass using only even numbers
test-allEven-evens : run (Test allEven on [ evens nats ] by isEven?)
test-allEven-evens = Pass

test-someEven : runVerbose (Test (Exists n ~ Property (Even n)) 
                            on [ nats ] 
                            by isEven?)
test-someEven = Pass (∃ ⟨ 0 ⟩ (Hold (Even 0)))

test-someEven-odds : run (Test (Exists n ~ Property (Even n)) 
                           on [ odds nats ] 
                           by isEven?)
test-someEven-odds = Failed

isSumEven? : (n : ℕ) -> (m : ℕ) -> Dec (Even (n + m))
isSumEven? n m = isEven? (n + m)

-- The order of the quantifiers is relevant:
-- For some fixed n, does it hold for all m that Even (n + m) ?
test-idem : runVerbose (Test Exists n ~ Forall m ~ Property (Even (n + m))
                        on nats ∷ (nats ∷ [])
                        by isSumEven?)
test-idem = Failed (¬∃ ℕ (∃ < ℕ > ✗))

-- Changing the order instead the property holds.
-- For all n, m can be found such that Even (n + m)
test-idem2 : runVerbose (Test Forall n ~ Exists m ~ Property (Even (n + m)) 
                         on nats ∷ (nats ∷ []) 
                         by isSumEven?)
test-idem2 = Pass (ForAll ℕ (∃ < ℕ > ✓))
