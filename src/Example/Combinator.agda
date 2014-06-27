module Example.Combinator where

open import Test hiding ( Test_on_by_ )
open import Test.StreamGenerator

open import Example.Simple
open import Example.Even

open import Data.Empty
open import Data.Nat using (ℕ ; _+_ ; suc ; zero ; _≟_)
open import Data.Stream
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (_≡_)

test-Not-imp : runVerbose (Test (Not impossible) on [] by (no (λ z → z))) 
test-Not-imp = Pass (DoesNotHold ⊥)

test-not-all-even : runVerbose (Test Not (Forall n ~ Property (Even n)) on [ nats ] by isEven?)
test-not-all-even = Pass (∃ ⟨ 1 ⟩ (DoesNotHold (Even 1)))

test-not-one-eq-zero : run (Test (Forall n ~ Not (Forall m ~ Property (n ≡ m))) 
                       on nats ∷ nats ∷ [] 
                       by Data.Nat._≟_)
test-not-one-eq-zero = Pass

test-not-one-eq-zero' : runVerbose (Test (Forall n ~ (Forall m ~ (Not (Property (n ≡ m))))) 
                        on nats ∷ nats ∷ [] by Data.Nat._≟_)
test-not-one-eq-zero' = Failed (∃ ⟨ 0 ⟩ (∃ ⟨ 0 ⟩ (Hold (0 ≡ 0))))

test-not-one-eq-zero'' : runVerbose (Test (Not (Forall n ~ (Forall m ~ (Property (n ≡ m))))) 
                         on nats ∷ nats ∷ [] by Data.Nat._≟_)
test-not-one-eq-zero'' = Pass (∃ ⟨ 0 ⟩ (∃ ⟨ 1 ⟩ (DoesNotHold (0 ≡ 1))))

test-double-neg : runVerbose (Test (Not (Forall n ~ (Forall m ~ (Not (Property (n ≡ m)))))) 
                  on nats ∷ nats ∷ [] by Data.Nat._≟_)
test-double-neg = Pass (∃ ⟨ 0 ⟩ (∃ ⟨ 0 ⟩ (Hold (0 ≡ 0))))

unique-pass : run (Test Exists! n ~ Forall m ~ Property (n + m ≡ m) on nats ∷ (nats ∷ []) 
              by (\ x y -> Data.Nat._≟_ (x + y) y))
unique-pass = Pass

unique-fail : runVerbose (Test Exists! n ~ Property (Even n) on [ nats ] by isEven?)
unique-fail = Failed (NotUnique ⟨ 0 ⟩ ~ Hold (Even 0) & ⟨ 2 ⟩ ~ Hold (Even 2))

open import Data.Product

-- shorthand 
⟪_⟫ : ∀ {a b} {A : Set a} {P : A -> Set b} -> (f : (x : A) -> P x) -> ((x : A) -> Σ (P x) (λ _ → P x))
⟪ f ⟫ = <_,_> f f

disj1 : run (Test Forall n ~ (Property (Even n)) ∨ Not (Property (Even n)) 
        on nats ∷ ([] , []) by ⟪ isEven? ⟫)
disj1 = Pass

disj1' : runVerbose (Test Forall n ~ (Property (Even n)) ∨ Not (Property (Even n)) 
        on nats ∷ ([] , []) by ⟪ isEven? ⟫)
disj1' = Pass (ForAll ℕ (Fst ✓))

disj2 : run (Test Forall n ~ (Property (Even n)) ∨ (Exists m ~ Property (Even (n + m))) 
            on (odds nats) ∷ ([] , (nats ∷ [])) 
            by <_,_> isEven? (λ n m -> isEven? (n + m)))
disj2 = Pass

disj3 : runVerbose (Test (Property (Even 1)) ∨ Not (Property (Even 0)) 
        on ([] , [])
        by (isEven? 1 , isEven? 0) )
disj3 = Failed (DoesNotHold (Even (suc zero)) And Hold (Even zero))

impl0 : run (Test Forall n ~ (Property (Even n)) ⇒ Property (Even (n + 2))
        on nats ∷ ([] , [])
        by <_,_> isEven? (λ n -> isEven? (n + 2)))
impl0 = Pass

impl1 : runVerbose (Test Forall n ~ (Property (Even n)) ⇒ Property (Even (n + 2))
        on nats ∷ ([] , [])
        by <_,_> isEven? (λ n -> isEven? (n + 2)))
impl1 = Pass (ForAll ℕ (Snd ✓))

impl2 : runVerbose (Test Forall n ~ (Property (Even n)) ⇒ Property (Even (n + 1))
        on nats ∷ ([] , [])
        by <_,_> isEven? (λ n -> isEven? (n + 1)))
impl2 = Failed (Test.∃ ⟨ 0 ⟩ (Hold (Even 0) And DoesNotHold (Even 1)))

impl3 : runVerbose (Test Forall n ~ (Property (Even n)) ⇒ Property (Even (n + 2))
        on (odds nats) ∷ ([] , [])
        by <_,_> isEven? (λ n -> isEven? (n + 2)))
impl3 = Pass (ForAll ℕ (Fst ✗))

conj1 : runVerbose (Test Exists! n ~ (Property (Even n)) ∧ Property (n + n ≡ n)
        on nats ∷ ([] , [])
        by ( <_,_> isEven? (λ n → n + n ‌≟ n)))
conj1 = Pass (Test.∃! ⟨ 0 ⟩ (Hold (Even 0) And Hold (0 ≡ 0)))

open import Function hiding (_⟨_⟩_) 

conj2 : run (Test Exists n ~ (Property (Even n)) ∧ (Property (Even (1 + n)))
        on nats ∷ ([] , [])
        by <_,_> isEven? (isEven? ∘ suc))
conj2 = Failed

conj2' : runVerbose (Test Forall n ~ (Property (Even n)) ∧ (Property (Even (1 + n)))
        on nats ∷ ([] , [])
        by <_,_> isEven? (isEven? ∘ suc))
conj2' = Failed (Test.∃ ⟨ 0 ⟩ (Snd (DoesNotHold (Even 1))))

conj2'' : run (Test Forall n ~ (Property (Even n)) ∨ (Property (Even (1 + n)))
        on nats ∷ ([] , [])
        by  <_,_> isEven? (isEven? ∘ suc))
conj2'' = Pass

iff1 : run (Test Forall n ~ (Property (Even n)) ⇔ (Not (Property (Even (1 + n))))
           on nats ∷ (([] , []) , ([] , []))
           by <_,_> (<_,_> isEven? (isEven? ∘ suc)) ((<_,_> (isEven? ∘ suc) isEven?)) )
iff1 = Pass

iff2-fail : runVerbose (Test Forall n ~ (Property (Even n)) ⇔ (Property (Even (n + n)))
                on nats ∷ (([] , []) , ([] , []))
                by <_,_> (<_,_> isEven? (λ n -> isEven? (n + n))) (<_,_> (λ n -> isEven? (n + n)) isEven?) )
iff2-fail = Failed (Test.∃ ⟨ 1 ⟩ (Snd (Hold (Even 2) And DoesNotHold (Even 1))))
