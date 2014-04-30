module Example where

open import Base
open import Coinduction
open import Data.Nat
open import Data.Stream
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

test-even-double : Pass
test-even-double = {!unquote (test { \ n -> Even n } 10 nats isEven? ) !}

-- It will raise an error at compile time 
test-all-even : Pass
test-all-even = {!unquote (test {Even} 2 nats isEven?)!}
