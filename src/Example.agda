module Example where

open import Base hiding (Test_on_by_and_)
import Base as B
open import StreamGenerator 
open import Coinduction
open import Data.Nat
open import Data.Stream hiding (take)
open import Data.Product as P hiding ( ∃ )
open import Data.List hiding (take ; [_] )
open import Data.Unit 
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding ( [_] )
open import Relation.Nullary

-- Examples using explicit lists

lists : List (List ℕ)
lists = [] ∷ (1 ∷ []) ∷ []

-- Input stream, all the natural numbers
nats : Stream ℕ
nats = go 0
  where 
    go : ℕ -> Stream ℕ
    go n = n ∷ ♯ (go (n + 1))

-- Constant property

trivial : U []
trivial = Property Unit

dec-trivial : ⟦ trivial ⟧
dec-trivial = yes unit

test-trivial : runVerbose (Test trivial on [] by dec-trivial and Unit )
test-trivial = Pass (Hold Unit)

impossible : U []
impossible = Property ⊥

dec-impossible : ⟦ impossible ⟧
dec-impossible = no (λ z → z)

test-impossible : runVerbose (Test impossible on [] by dec-impossible and ⊥)
test-impossible = Failed (DoesNotHold ⊥)

skip-impossible : skip (Test impossible on [] by dec-impossible and ⊥)
skip-impossible = Skipped

ex1 : U (ℕ ∷ []) 
ex1 = Forall {ℕ} (λ n -> Property (n ≡ n))

dec-ex1 : ⟦ ex1 ⟧
dec-ex1 = λ x -> Data.Nat._≟_ x x

test-ex1 : run (B.Test ex1 on [ take 10 nats ] by dec-ex1 and (λ n → n ≡ n)) 
test-ex1 = Pass

ex : U (ℕ ∷ List ℕ ∷ [])
ex =  (Forall (λ n -> Exists {List ℕ} (λ xs -> Property (n ≡ (length xs)))))

dec-ex : ⟦ ex ⟧
dec-ex = λ n xs → Data.Nat._≟_ n (length xs)

test-ex : runVerbose (B.Test ex on ((take 2 nats) ∷ lists ∷ []) by dec-ex and (λ n xs → n ≡ (length xs) ))
test-ex = Pass (Forall ℕ (Exists (suc zero ∷ []) (Hold (suc zero ≡ suc zero))))

--------------------------------------------------------------------------------
-- Example definitions and lemmas
--------------------------------------------------------------------------------

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

test-even-double : run (Test Forall (λ n → Property (Even (n + n))) on [ nats ] by (λ n → isEven? (n + n)) and (λ n → Even (n + n)) )
test-even-double = Pass

test-all-even : runVerbose (Test (Forall (λ n → Property (Even n))) on [ nats ] by isEven? and (λ n → Even n))
test-all-even = Failed (NotFor (suc zero) (DoesNotHold (Even (suc zero))))

test-all-even-evens : run (Test Forall (λ n → Property (Even n)) on  [ evens nats ] by isEven? and (λ n → Even n))
test-all-even-evens = Pass

test-some-even : runVerbose (Test Exists (λ n → Property (Even n)) on [ nats ] by isEven? and (λ n → Even n))
test-some-even = Pass (Exists zero (Hold (Even zero)))

test-some-even-odds : run (Test (Exists (λ n → Property (Even n))) on [ odds nats ] by isEven? and (λ n → Even n))
test-some-even-odds = Failed

--------------------------------------------------------------------------------
-- Arithmetics with naturals 
--------------------------------------------------------------------------------

test-all-sym-plus  : run (Test Forall (λ n → Forall (λ m → Property (n + m ≡ m + n))) on 
                         (nats ∷ nats ∷ []) by (λ n m → (n + m) Data.Nat.≟ (m + n)) and (λ n m → n + m ≡ m + n) )
test-all-sym-plus = Pass

test-all-false-equality : runVerbose (Test (Forall (λ n → Forall (λ m → Property (n ≡ m)))) on 
                              (nats ∷ nats ∷ []) by Data.Nat._≟_ and (λ n m → n ≡ m))
test-all-false-equality = Failed
                            (NotFor zero
                             (NotFor (suc zero) (DoesNotHold (zero ≡ suc zero))))

--------------------------------------------------------------------------------
-- Pretty syntax
--------------------------------------------------------------------------------

test-pretty : U (ℕ ∷ [])
test-pretty = Forall n ~ (Property (n ≡ n))

test-pretty2 : U (ℕ ∷ List ℕ ∷ [])
test-pretty2 =  Forall n ~ Exists xs ~ (Property (n ≡ (length xs)))

--------------------------------------------------------------------------------
-- Testing new constructs
--------------------------------------------------------------------------------

test-Not-imp : runVerbose (Test_on_by_and_ (Not impossible) [] (no (λ z → z)) ⊥) 
test-Not-imp = Pass (DoesNotHold ⊥)

test-not-all-even : runVerbose (Test Not (Forall n ~ Property (Even n)) on [ nats ] by isEven? and Even)
test-not-all-even = Pass (NotFor (suc zero) (DoesNotHold (Even (suc zero))))

test-not-one-eq-zero : run (Test (Forall n ~ Not (Forall m ~ Property (n ≡ m))) 
                       on nats ∷ nats ∷ [] by Data.Nat._≟_ and _≡_)
test-not-one-eq-zero = Pass

test-not-one-eq-zero' : runVerbose (Test (Forall n ~ (Forall m ~ (Not (Property (n ≡ m))))) 
                        on nats ∷ nats ∷ [] by Data.Nat._≟_ and _≡_)
test-not-one-eq-zero' = Failed (NotFor zero (NotFor zero (Hold (zero ≡ zero))))

test-not-one-eq-zero'' : runVerbose (Test (Not (Forall n ~ (Forall m ~ (Property (n ≡ m))))) 
                         on nats ∷ nats ∷ [] by Data.Nat._≟_ and _≡_)
test-not-one-eq-zero'' = Pass
                           (NotFor zero (NotFor (suc zero) (DoesNotHold (zero ≡ suc zero))))

test-double-neg : runVerbose (Test (Not (Forall n ~ (Forall m ~ (Not (Property (n ≡ m)))))) 
                  on nats ∷ nats ∷ [] by Data.Nat._≟_ and _≡_)
test-double-neg = Pass (NotFor zero (NotFor zero (Hold (zero ≡ zero))))

unique-pass : run (Test Exists! n ~ Forall m ~ Property (n + m ≡ m) on nats ∷ (nats ∷ []) 
              by (\ x y -> Data.Nat._≟_ (x + y) y) and (\ n m -> n + m ≡ m))
unique-pass = Pass

-- TODO wrong result
unique-fail : runVerbose (Test Exists! n ~ Property (Even n) on [ nats ] by isEven? and Even)
unique-fail = Pass
                (NotUnique zero ~ Hold (Even zero) & suc (suc zero) ~
                 Hold (Even (suc (suc zero))))


disj1 : run (Test Forall n ~ (Property (Even n)) ∨ Not (Property (Even n)) 
        on nats ∷ ([] , []) by (λ n → (isEven? n) , (isEven? n)) 
        and (λ n → (Even n) , (Even n)))
disj1 = Pass

disj2 : run (Test Forall n ~ (Property (Even n)) ∨ (Exists m ~ Property (Even (n + m))) 
            on (odds nats) ∷ ([] , (nats ∷ [])) 
            by (λ n → (isEven? n) , (λ m → isEven? (n + m)))
            and (λ n → (Even n) , (λ m → Even (n + m)))) 
disj2 = Pass

disj3 : runVerbose (Test (Property (Even 1)) ∨ Not (Property (Even 0)) 
        on [] , [] 
        by (isEven? 1) , isEven? 0
        and ((Even 1) , Even 0))
disj3 = Failed (DoesNotHold (Even (suc zero)) And Hold (Even zero))

impl1 : run (Test Forall n ~ (Property (Even n)) ⇒ Property (Even (n + 2))
        on nats ∷ ([] , [])
        by (λ n → (isEven? n) , (isEven? (n + 2)))
        and (λ n → (Even n) , (Even (n + 2))))
impl1 = Pass

conj1 : runVerbose (Test Exists! n ~ (Property (Even n)) ∧ Property (n + n ≡ n)
        on nats ∷ ([] , [])
        by (λ n → (isEven? n) , (n + n Data.Nat.≟ n))
        and (λ n → (Even n) , (n + n ≡ n)))
conj1 = Pass (ExistsUnique zero (Hold (Even zero) And Hold (zero ≡ zero)))

conj2 : run (Test Exists n ~ (Property (Even n)) ∧ (Property (Even (n + 1)))
        on nats ∷ ([] , [])
        by (λ n → (isEven? n) , (isEven? (n + 1)))
        and (λ n → (Even n) , (Even (n + 1))))
conj2 = Failed

conj2' : runVerbose (Test Forall n ~ (Property (Even n)) ∧ (Property (Even (n + 1)))
        on nats ∷ ([] , [])
        by (λ n → (isEven? n) , (isEven? (n + 1)))
        and (λ n → (Even n) , (Even (n + 1))))
conj2' = Failed (NotFor zero (DoesNotHold (Even (suc zero))))

conj2'' : run (Test Forall n ~ (Property (Even n)) ∨ (Property (Even (n + 1)))
        on nats ∷ ([] , [])
        by (λ n → (isEven? n) , (isEven? (n + 1)))
        and (λ n → (Even n) , (Even (n + 1))))
conj2'' = Pass

iff1 : run (Test Forall n ~ (Property (Even n)) ⇔ (Not (Property (Even (n + 1))))
           on nats ∷ (([] , []) , ([] , []))
           by (λ n → ((isEven? n) , (isEven? (n + 1))) , ((isEven? (n + 1)) , isEven? n))
           and (λ n → ((Even n) , (Even (n + 1))) , ((Even (n + 1)) , (Even n))))
iff1 = Pass

iff2-fail : runVerbose (Test Forall n ~ (Property (Even n)) ⇔ (Property (Even (n + n)))
                on nats ∷ (([] , []) , ([] , []))
                by (λ n → ((isEven? n) , (isEven? (n + n))) , ((isEven? (n + n)) , (isEven? n)))
                and (λ n → ((Even n) , (Even (n + n))) , ((Even (n + n)) , (Even n))))
iff2-fail = Failed
              (NotFor (suc zero)
               (Hold (Even (suc (suc zero))) And DoesNotHold (Even (suc zero))))


--------------------------------------------------------------------------------
-- Examples using different test runners
--------------------------------------------------------------------------------

double-even : pass (Test Forall n ~ Property (Even (n + n)) on nats ∷ [] 
                   by (λ n → isEven? (n + n)) and (λ n → Even (n + n)))
double-even = Pass

next-even : fail (Test Forall n ~ Property (Even (n + 1)) on nats ∷ [] 
                 by (λ n → isEven? (n + 1)) and (λ n → Even (n + 1)))
next-even = Pass

--------------------------------------------------------------------------------
-- Shows the effects of good and bad choices of < u >
--------------------------------------------------------------------------------

u : U (ℕ ∷ ℕ ∷ [])
u = Forall n ~ Forall m ~ Property (Even (n + m))

good : < u > 
good = λ n m → Even (n + m)

bad1 : < u >
bad1 = λ n m -> Even m

bad2 : < u >
bad2 = λ n m → ⊤

test-u-good : runVerbose (B.Test u
                on (1 ∷ 2 ∷ 3 ∷ []) ∷ (1 ∷ 2 ∷ 3 ∷ []) ∷ []
                by (λ n m → isEven? (n + m))
                and good )
test-u-good = Failed
                (NotFor (suc zero)
                 (NotFor (suc (suc zero))
                  (DoesNotHold (Even (suc (suc (suc zero)))))))

test-u-bad1 : runVerbose (B.Test u
                on (1 ∷ 2 ∷ 3 ∷ []) ∷ (1 ∷ 2 ∷ 3 ∷ []) ∷ []
                by (λ n m → isEven? (n + m))
                and bad1 )
test-u-bad1 = Failed
                (NotFor (suc zero)
                 (NotFor (suc (suc zero)) (DoesNotHold (Even (suc (suc zero))))))

test-u-bad2 : runVerbose (B.Test u
                on (1 ∷ 2 ∷ 3 ∷ []) ∷ (1 ∷ 2 ∷ 3 ∷ []) ∷ []
                by (λ n m → isEven? (n + m))
                and bad2 )
test-u-bad2 = Failed
                (NotFor (suc zero) (NotFor (suc (suc zero)) (DoesNotHold ⊤)))
