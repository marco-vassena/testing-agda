module Example where

open import Base
open import Coinduction
open import Data.Nat
open import Data.Stream hiding (take)
open import Data.Product as P hiding ( ∃ )
open import Data.List hiding (take)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

--------------------------------------------------------------------------------
-- Example definitions and lemmas
--------------------------------------------------------------------------------

data Even  : ℕ → Set where
  isEven0  : Even 0
  isEven+2 : ∀ {n} → Even n → Even (suc (suc n))

-- The lemmas I would like to test before starting proving
even-double : (n : ℕ) -> Even ( n + n )
even-double zero = isEven0
even-double (suc n) = {!!}

all-even : (n : ℕ) -> Even n
all-even n = {!!}

some-even : P.∃ Even
some-even = zero P., isEven0

-- Even is a decidable property.
isEven? : (n : ℕ) -> Dec (Even n)
isEven? zero = yes isEven0
isEven? (suc zero) = no (λ ())
isEven? (suc (suc n)) with isEven? n
isEven? (suc (suc n)) | yes p = yes (isEven+2 p)
isEven? (suc (suc n)) | no ¬p = no ( \ p -> ¬p (unpack p) )
  where unpack : ∀ {n} -> Even (suc (suc n)) -> Even n
        unpack (isEven+2 r) = r

-- Input stream, all the natural numbers
nats : Stream ℕ
nats = go 0
  where 
    go : ℕ -> Stream ℕ
    go n = n ∷ ♯ (go (n + 1))


--------------------------------------------------------------------------------
-- Test cases
--------------------------------------------------------------------------------

test-even-double : forAll (take 10 nats) (Lemma isEven? even-double)
test-even-double = Ok

test-all-even : forAll (take 10 nats) (Lemma isEven? all-even)
test-all-even = CounterExample (suc zero)

test-all-even-evens : forAll (take 10 (evens nats)) (Lemma isEven? all-even)
test-all-even-evens = Ok

test-some-even : ∃ (take 10 nats) (Lemma isEven? some-even)
test-some-even = Exists zero

test-some-even-odds : ∃ (take 10 (odds nats)) (Lemma isEven? some-even) 
test-some-even-odds = {!!}


--------------------------------------------------------------------------------
-- Arithmetics with naturals 
--------------------------------------------------------------------------------

eq1-ℕ : (n : ℕ) -> Dec (n ≡ n)
eq1-ℕ n = yes refl

reflexivity : ∀ (n : ℕ) -> n ≡ n
reflexivity n = refl

test-all-refl : forAll (take 10 nats) (Lemma eq1-ℕ reflexivity)
test-all-refl = Ok

-- The uncurried version cannot be tested directly.
eq2-ℕ : (n m : ℕ) -> Dec (n ≡ m)
eq2-ℕ = {!!}

sym-plus : ∀ (n m : ℕ) -> (n + m) ≡ (m + n)
sym-plus n m = {!!}

-- You need to pack everything together, but then also the
-- lemma must use it, which is cumbersome
eq2'-ℕ : (p : ℕ × ℕ) -> let (n , m) = p in Dec (n ≡ m)
eq2'-ℕ (n , m) = n ≟ m

sym-plus' : (p : ℕ × ℕ) -> let (n , m) = p in n + m ≡ m + n
sym-plus' (n , m) = sym-plus n m

input : List (ℕ × ℕ)
input = (0 , 0) ∷ (0 , 1) ∷ (1 , 0) ∷ (1 , 1) ∷ []

test-all-sym-plus  : forAll input (Lemma eq2'-ℕ sym-plus')
test-all-sym-plus = Ok

false-equality : (p : ℕ × ℕ) -> let (n , m) = p in ((n + m + 1) ≡ n + m)
false-equality = {!!}

test-all-false-equality : forAll input (Lemma eq2'-ℕ false-equality)
test-all-false-equality = CounterExample (zero , zero)
