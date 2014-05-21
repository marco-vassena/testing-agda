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

test-trivial : run (Test trivial on [] by dec-trivial and Unit )
test-trivial = Pass (Hold Unit)

impossible : U []
impossible = Property ⊥

dec-impossible : ⟦ impossible ⟧
dec-impossible = no (λ z → z)

test-impossible : run (Test impossible on [] by dec-impossible and ⊥)
test-impossible = Failed (DoesNotHold ⊥)

skip-impossible : skip (Test impossible on [] by dec-impossible and ⊥)
skip-impossible = Skipped

ex1 : U (ℕ ∷ []) 
ex1 = Forall {ℕ} (λ n -> Property (n ≡ n))

dec-ex1 : ⟦ ex1 ⟧
dec-ex1 = λ x -> Data.Nat._≟_ x x

test-ex1 : run (B.Test ex1 on [ take 10 nats ] by dec-ex1 and (λ n → n ≡ n)) 
test-ex1 = Pass (Forall ℕ (Hold (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ≡
                                   suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))  
-- The result from the last case is returned

ex : U (ℕ ∷ List ℕ ∷ [])
ex =  (Forall (λ n -> Exists {List ℕ} (λ xs -> Property (n ≡ (length xs)))))

dec-ex : ⟦ ex ⟧
dec-ex = λ n xs → Data.Nat._≟_ n (length xs)

test-ex : run (B.Test ex on ((take 2 nats) ∷ lists ∷ []) by dec-ex and (λ n xs → n ≡ (length xs) ))
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
                     (Forall ℕ
                      (Hold (Even (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))

test-all-even : run (Test (Forall (λ n → Property (Even n))) on [ nats ] by isEven? and (λ n → Even n))
test-all-even = Failed (NotFor (suc zero) (DoesNotHold (Even (suc zero))))

test-all-even-evens : run (Test Forall (λ n → Property (Even n)) on  [ evens nats ] by isEven? and (λ n → Even n))
test-all-even-evens = Pass
                        (Forall ℕ
                         (Hold (Even (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))

test-some-even : run (Test Exists (λ n → Property (Even n)) on [ nats ] by isEven? and (λ n → Even n))
test-some-even = Pass (Exists zero (Hold (Even zero)))

test-some-even-odds : run (Test (Exists (λ n → Property (Even n))) on [ odds nats ] by isEven? and (λ n → Even n))
test-some-even-odds = Failed
                        (NotExists ℕ
                         (DoesNotHold (Even (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))

--------------------------------------------------------------------------------
-- Arithmetics with naturals 
--------------------------------------------------------------------------------

test-all-sym-plus  : run (Test Forall (λ n → Forall (λ m → Property (n + m ≡ m + n))) on 
                         (nats ∷ nats ∷ []) by (λ n m → (n + m) Data.Nat.≟ (m + n)) and (λ n m → n + m ≡ m + n) )
test-all-sym-plus = Pass (Forall ℕ (Forall ℕ (Hold (suc (suc (suc (suc (suc (suc (suc (suc zero))))))) ≡
                                                      suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))

test-all-false-equality : run (Test (Forall (λ n → Forall (λ m → Property (n ≡ m)))) on 
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

test-Not-imp : run (Test_on_by_and_ (Not impossible) [] (no (λ z → z)) ⊥) 
test-Not-imp = Pass (DoesNotHold ⊥)

test-not-all-even : run (Test Not (Forall n ~ Property (Even n)) on [ nats ] by isEven? and Even)
test-not-all-even = Pass (NotFor (suc zero) (DoesNotHold (Even (suc zero))))

test-not-one-eq-zero : run (Test (Forall n ~ Not (Forall m ~ Property (n ≡ m))) on nats ∷ nats ∷ [] by Data.Nat._≟_ and _≡_)
test-not-one-eq-zero = Pass
                         (Forall ℕ
                          (NotFor zero (DoesNotHold (suc (suc (suc (suc zero))) ≡ zero))))

test-not-one-eq-zero' : run (Test (Forall n ~ (Forall m ~ (Not (Property (n ≡ m))))) on nats ∷ nats ∷ [] by Data.Nat._≟_ and _≡_)
test-not-one-eq-zero' = Failed (NotFor zero (NotFor zero (Hold (zero ≡ zero))))

test-not-one-eq-zero'' : run (Test (Not (Forall n ~ (Forall m ~ (Property (n ≡ m))))) on nats ∷ nats ∷ [] by Data.Nat._≟_ and _≡_)
test-not-one-eq-zero'' = Pass
                           (NotFor zero (NotFor (suc zero) (DoesNotHold (zero ≡ suc zero))))

test-double-neg : run (Test (Not (Forall n ~ (Forall m ~ (Not (Property (n ≡ m)))))) on nats ∷ nats ∷ [] by Data.Nat._≟_ and _≡_)
test-double-neg = Pass (NotFor zero (NotFor zero (Hold (zero ≡ zero))))

unique-pass : run (Test Exists! n ~ Forall m ~ Property (n + m ≡ m) on nats ∷ (nats ∷ []) 
              by (\ x y -> Data.Nat._≟_ (x + y) y) and (\ n m -> n + m ≡ m))
unique-pass = Pass
                (ExistsUnique zero
                 (Forall ℕ
                  (Hold (suc (suc (suc (suc zero))) ≡ suc (suc (suc (suc zero)))))))

unique-fail : run (Test Exists! n ~ Property (Even n) on [ nats ] by isEven? and Even)
unique-fail = Pass
                (NotUnique zero ~ Hold (Even zero) & suc (suc zero) ~
                 Hold (Even (suc (suc zero))))


disj1 : run (Test Forall n ~ (Property (Even n)) ∨ Not (Property (Even n)) on nats ∷ ([] , []) by (λ n → (isEven? n) , (isEven? n)) and (λ n → (Even n) , (Even n)))
disj1 = Pass (Forall ℕ (Hold (Even (suc (suc (suc (suc zero)))))))

disj2 : run (Test Forall n ~ (Property (Even n)) ∨ (Exists m ~ Property (Even (n + m))) 
            on (odds nats) ∷ ([] , (nats ∷ [])) 
            by (λ n → (isEven? n) , (λ m → isEven? (n + m)))
            and (λ n → (Even n) , (λ m → Even (n + m)))) 
disj2 = Pass
          (Forall ℕ
           (Exists (suc zero)
            (Hold
             (Even
              (suc
               (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))


disj3 : run (Test (Property (Even 1)) ∨ Not (Property (Even 0)) 
        on [] , [] 
        by (isEven? 1) , isEven? 0
        and ((Even 1) , Even 0))
disj3 = Failed (DoesNotHold (Even (suc zero)) And Hold (Even zero))
