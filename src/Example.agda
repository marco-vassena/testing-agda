module Example where

open import Base
open import Coinduction
open import Data.Nat
open import Data.Stream hiding (take)
open import Data.Product using ( ∃ )
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

data Even  : ℕ →  Set where
  isEven0  : Even 0
  isEven+2 : ∀ {n} → Even n → Even (suc (suc n))

-- The lemma I would like to test before starting proving
even-double : (n : ℕ) -> Even ( n + n )
even-double zero = isEven0
even-double (suc n) = {!!}

-- Here I should find a counter example
all-even : (n : ℕ) -> Even n
all-even n = {!!}

some-even : ∃ Even
some-even = zero Data.Product., isEven0

isEven? : (n : ℕ) -> Dec (Even n)
isEven? zero = yes isEven0
isEven? (suc zero) = no (λ ())
isEven? (suc (suc n)) with isEven? n
isEven? (suc (suc n)) | yes p = yes (isEven+2 p)
isEven? (suc (suc n)) | no ¬p = no ( \ p -> ¬p (unpack p) )
  where unpack : ∀ {n} -> Even (suc (suc n)) -> Even n
        unpack (isEven+2 r) = r

nats : Stream ℕ
nats = go 0
  where 
    go : ℕ -> Stream ℕ
    go n = n ∷ ♯ (go (n + 1))

test-even-double : allTrue (take 10 nats) (Lemma isEven? even-double)
test-even-double = Ok

test-all-even : allTrue (take 10 nats) (Lemma isEven? all-even)
test-all-even = {!!}

test-some-even : ∃True (take 10 nats) (Lemma isEven? some-even)
test-some-even = Exists zero
