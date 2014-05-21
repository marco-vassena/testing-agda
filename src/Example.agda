module Example where

open import Base hiding (Test_on_by_)
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

test-trivial : run (Test trivial on [] by dec-trivial )
test-trivial = Pass (RP (Hold unit))

impossible : U []
impossible = Property ⊥

dec-impossible : ⟦ impossible ⟧
dec-impossible = no (λ z → z)

test-impossible : run (Test impossible on [] by dec-impossible)
test-impossible = Failed (RP (DoesNotHold (λ z → z)))

skip-impossible : skip (Test impossible on [] by dec-impossible)
skip-impossible = Skipped

ex1 : U (ℕ ∷ []) 
ex1 = Forall {ℕ} (λ n -> Property (n ≡ n))

dec-ex1 : ⟦ ex1 ⟧
dec-ex1 = λ x -> Data.Nat._≟_ x x

test-ex1 : run (B.Test ex1 on [ take 10 nats ] by dec-ex1 ) 
test-ex1 = Pass (RA (Forall ℕ (RP (Hold refl))))

ex : U (ℕ ∷ List ℕ ∷ [])
ex =  (Forall (λ n -> Exists {List ℕ} (λ xs -> Property (n ≡ (length xs)))))

dec-ex : ⟦ ex ⟧
dec-ex = λ n xs → Data.Nat._≟_ n (length xs)

test-ex : run (B.Test ex on ((take 2 nats) ∷ lists ∷ []) by dec-ex )
test-ex = Pass (RA (Forall ℕ (RE (Exists (suc zero ∷ []) (RP (Hold refl))))))

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

test-even-double : run (Test Forall (λ n → Property (Even (n + n))) on [ nats ] by (λ n → isEven? (n + n)))
test-even-double = Pass
                     (RA
                      (Forall ℕ
                       (RP (Hold (isEven+2 (isEven+2 (isEven+2 (isEven+2 isEven0))))))))

test-all-even : run (Test (Forall (λ n → Property (Even n))) on [ nats ] by isEven?)
test-all-even = Failed (RA (NotFor (suc zero) (RP (DoesNotHold _))))

test-all-even-evens : run (Test Forall (λ n → Property (Even n)) on  [ evens nats ] by isEven?)
test-all-even-evens = Pass
                        (RA
                         (Forall ℕ
                          (RP (Hold (isEven+2 (isEven+2 (isEven+2 (isEven+2 isEven0))))))))

test-some-even : run (Test Exists (λ n → Property (Even n)) on [ nats ] by isEven?)
test-some-even = Pass (RE (Exists zero (RP (Hold isEven0))))

test-some-even-odds : run (Test (Exists (λ n → Property (Even n))) on [ odds nats ] by isEven?)
test-some-even-odds = Failed
                        (RE
                         (NotExists ℕ
                          (RP
                           (DoesNotHold _ ))))  -- TODO : the failure proof is completely dumped here as a huge lambda

--------------------------------------------------------------------------------
-- Arithmetics with naturals 
--------------------------------------------------------------------------------

test-all-sym-plus  : run (Test Forall (λ n → Forall (λ m → Property (n + m ≡ m + n))) on 
                         (nats ∷ nats ∷ []) by (λ n m → (n + m) Data.Nat.≟ (m + n)))
test-all-sym-plus = Pass (RA (Forall ℕ (RA (Forall ℕ (RP (Hold refl))))))

test-all-false-equality : run (Test (Forall (λ n → Forall (λ m → Property (n ≡ m)))) on 
                              (nats ∷ nats ∷ []) by Data.Nat._≟_)
test-all-false-equality = Failed
                            (RA
                             (NotFor zero
                              (RA
                               (NotFor (suc zero) (RP (DoesNotHold _)))))) 

--------------------------------------------------------------------------------
-- Pretty syntax
--------------------------------------------------------------------------------

test-pretty : U (ℕ ∷ [])
test-pretty = Forall n ~ (Property (n ≡ n))

test-pretty2 : U (ℕ ∷ List ℕ ∷ [])
test-pretty2 =  Forall n ~ Exists xs ~ (Property (n ≡ (length xs)))
