-- Examples with Even property

module Example.Even where

open import Test hiding (Test_on_by_)
open import Test.StreamGenerator

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
test-all-even = Failed (NotFor (suc zero) (DoesNotHold (Even (suc zero))))

test-all-even-evens : run (Test Forall (λ n → Property (Even n)) on  [ evens nats ] by isEven?)
test-all-even-evens = Pass

test-some-even : runVerbose (Test Exists (λ n → Property (Even n)) on [ nats ] by isEven?)
test-some-even = Pass (Exists zero (Hold (Even zero)))

test-some-even-odds : run (Test (Exists (λ n → Property (Even n))) on [ odds nats ] by isEven?)
test-some-even-odds = Failed

--------------------------------------------------------------------------------
-- Arithmetics with naturals 
--------------------------------------------------------------------------------

test-all-sym-plus  : run (Test Forall (λ n → Forall (λ m → Property (n + m ≡ m + n))) on 
                         (nats ∷ nats ∷ []) by (λ n m → (n + m) Data.Nat.≟ (m + n)))
test-all-sym-plus = Pass

test-all-false-equality : runVerbose (Test (Forall (λ n → Forall (λ m → Property (n ≡ m)))) on 
                              (nats ∷ nats ∷ []) by Data.Nat._≟_)
test-all-false-equality = Failed
                            (NotFor zero
                             (NotFor (suc zero) (DoesNotHold (zero ≡ suc zero))))
