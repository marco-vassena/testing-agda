module Example.Combinator where

open import Test.Base
open import Test.Runner
open import Test.Result
open import Test.Tester hiding (Test_on_by_)
open import Test.StreamGenerator

open import Example.Simple
open import Example.Even

open import Data.Empty
open import Relation.Nullary

test-Not-imp : runVerbose (Test (Not impossible) on [] by (no (λ z → z))) 
test-Not-imp = Pass (DoesNotHold ⊥)

test-not-all-even : runVerbose (Test Not (Forall n ~ Property (Even n)) on [ nats ] by isEven?)
test-not-all-even = Pass (NotFor (suc zero) (DoesNotHold (Even (suc zero))))

test-not-one-eq-zero : run (Test (Forall n ~ Not (Forall m ~ Property (n ≡ m))) 
                       on nats ∷ nats ∷ [] 
                       by Data.Nat._≟_)
test-not-one-eq-zero = Pass

test-not-one-eq-zero' : runVerbose (Test (Forall n ~ (Forall m ~ (Not (Property (n ≡ m))))) 
                        on nats ∷ nats ∷ [] by Data.Nat._≟_)
test-not-one-eq-zero' = Failed (NotFor zero (NotFor zero (Hold (zero ≡ zero))))

test-not-one-eq-zero'' : runVerbose (Test (Not (Forall n ~ (Forall m ~ (Property (n ≡ m))))) 
                         on nats ∷ nats ∷ [] by Data.Nat._≟_)
test-not-one-eq-zero'' = Pass
                           (NotFor zero (NotFor (suc zero) (DoesNotHold (zero ≡ suc zero))))

test-double-neg : runVerbose (Test (Not (Forall n ~ (Forall m ~ (Not (Property (n ≡ m)))))) 
                  on nats ∷ nats ∷ [] by Data.Nat._≟_)
test-double-neg = Pass (NotFor zero (NotFor zero (Hold (zero ≡ zero))))

unique-pass : run (Test Exists! n ~ Forall m ~ Property (n + m ≡ m) on nats ∷ (nats ∷ []) 
              by (\ x y -> Data.Nat._≟_ (x + y) y))
unique-pass = Pass

unique-fail : runVerbose (Test Exists! n ~ Property (Even n) on [ nats ] by isEven?)
unique-fail = Failed
                (NotUnique zero ~ Hold (Even zero) & suc (suc zero) ~
                 Hold (Even (suc (suc zero))))


disj1 : run (Test Forall n ~ (Property (Even n)) ∨ Not (Property (Even n)) 
        on nats ∷ ([] , []) by (λ n → (isEven? n) , (isEven? n)))
disj1 = Pass

disj2 : run (Test Forall n ~ (Property (Even n)) ∨ (Exists m ~ Property (Even (n + m))) 
            on (odds nats) ∷ ([] , (nats ∷ [])) 
            by (λ n → (isEven? n) , (λ m → isEven? (n + m))))
disj2 = Pass

disj3 : runVerbose (Test (Property (Even 1)) ∨ Not (Property (Even 0)) 
        on ([] , [])
        by ((isEven? 1) , isEven? 0))
disj3 = Failed (DoesNotHold (Even (suc zero)) And Hold (Even zero))

impl1 : run (Test Forall n ~ (Property (Even n)) ⇒ Property (Even (n + 2))
        on nats ∷ ([] , [])
        by (λ n → (isEven? n) , (isEven? (n + 2))))
impl1 = Pass

conj1 : runVerbose (Test Exists! n ~ (Property (Even n)) ∧ Property (n + n ≡ n)
        on nats ∷ ([] , [])
        by (λ n → (isEven? n) , (n + n Data.Nat.≟ n)))
conj1 = Pass (ExistsUnique zero (Hold (Even zero) And Hold (zero ≡ zero)))

conj2 : run (Test Exists n ~ (Property (Even n)) ∧ (Property (Even (n + 1)))
        on nats ∷ ([] , [])
        by (λ n → (isEven? n) , (isEven? (n + 1))))
conj2 = Failed

conj2' : runVerbose (Test Forall n ~ (Property (Even n)) ∧ (Property (Even (n + 1)))
        on nats ∷ ([] , [])
        by (λ n → (isEven? n) , (isEven? (n + 1))))
conj2' = Failed (NotFor zero (DoesNotHold (Even (suc zero))))

conj2'' : run (Test Forall n ~ (Property (Even n)) ∨ (Property (Even (n + 1)))
        on nats ∷ ([] , [])
        by (λ n → (isEven? n) , (isEven? (n + 1))))
conj2'' = Pass

iff1 : run (Test Forall n ~ (Property (Even n)) ⇔ (Not (Property (Even (n + 1))))
           on nats ∷ (([] , []) , ([] , []))
           by (λ n → ((isEven? n) , (isEven? (n + 1))) , ((isEven? (n + 1)) , isEven? n)))
iff1 = Pass

iff2-fail : runVerbose (Test Forall n ~ (Property (Even n)) ⇔ (Property (Even (n + n)))
                on nats ∷ (([] , []) , ([] , []))
                by (λ n → ((isEven? n) , (isEven? (n + n))) , ((isEven? (n + n)) , (isEven? n))))
iff2-fail = Failed
              (NotFor (suc zero)
               (Hold (Even (suc (suc zero))) And DoesNotHold (Even (suc zero))))
