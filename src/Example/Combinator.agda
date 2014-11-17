-- | Examples with different Predicate combinators

module Example.Combinator where

open import Test hiding ( Test_on_by_ )
open import Test.Input.Stream

open import Example.Simple
open import Example.Even
open import Example.Runner

open import Data.Empty
open import Data.Nat using (ℕ ; _+_ ; suc ; zero ; _≟_)
open import Data.Stream
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (_≡_)

test-Not-imp : runVerbose (Test (Not impossible) on [] by dec-impossible) 
test-Not-imp = Pass (DoesNotHold ⊥)

test-NotAllEven : runVerbose (Test (Not allEven) on [ nats ] by isEven?)
test-NotAllEven = Pass (∃ ⟨ 1 ⟩ (DoesNotHold (Even 1)))

test-not-one-eq-zero : run (Test (Forall n ~ Not (Forall m ~ Property (n ≡ m))) 
                       on nats ∷ nats ∷ [] 
                       by Data.Nat._≟_)
test-not-one-eq-zero = Pass

test-not-one-eq-zero' : runVerbose (Test (Forall n ~ (Forall m ~ (Not (Property (n ≡ m)))))
                                    on nats ∷ nats ∷ [] 
                                    by Data.Nat._≟_)
test-not-one-eq-zero' = Failed (∃ ⟨ 0 ⟩ (∃ ⟨ 0 ⟩ (Hold (0 ≡ 0))))

test-not-one-eq-zero'' : runVerbose (Test (Not (Forall n ~ (Forall m ~ (Property (n ≡ m))))) 
                                     on nats ∷ nats ∷ [] 
                                     by Data.Nat._≟_)
test-not-one-eq-zero'' = Pass (∃ ⟨ 0 ⟩ (∃ ⟨ 1 ⟩ (DoesNotHold (0 ≡ 1))))

test-doubleNot : runVerbose (Test (Not (Forall n ~ (Forall m ~ (Not (Property (n ≡ m)))))) 
                             on nats ∷ nats ∷ [] 
                             by Data.Nat._≟_)
test-doubleNot = Pass (∃ ⟨ 0 ⟩ (∃ ⟨ 0 ⟩ (Hold (0 ≡ 0))))

pass-∃unique : run (Test Exists! n ~ Forall m ~ Property (n + m ≡ m) 
                    on nats ∷ (nats ∷ []) 
                    by (\ x y -> Data.Nat._≟_ (x + y) y))
pass-∃unique = Pass

unique-fail : runVerbose (Test Exists! n ~ Property (Even n) on [ nats ] by isEven?)
unique-fail = Failed (NotUnique ⟨ 0 ⟩ ~ Hold (Even 0) & ⟨ 2 ⟩ ~ Hold (Even 2))

open import Data.Product

-- shorthand 
⟪_⟫ : ∀ {a b} {A : Set a} {P : A -> Set b} -> (f : (x : A) -> P x) -> ((x : A) -> Σ (P x) (λ _ → P x))
⟪ f ⟫ = <_,_> f f

disj1 : run (Test Forall n ~ (Property (Even n)) ∨ Not (Property (Even n)) 
             on nats ∷ ([] , []) 
             by ⟪ isEven? ⟫)
disj1 = Pass

disj1' : runVerbose (Test Forall n ~ (Property (Even n)) ∨ Not (Property (Even n)) 
                     on nats ∷ ([] , []) 
                     by ⟪ isEven? ⟫)
disj1' = Pass (ForAll ℕ (Fst ✓))

disj2 : run (Test Forall n ~ (Property (Even n)) ∨ (Exists m ~ Property (Even (n + m))) 
             on (odds nats) ∷ ([] , (nats ∷ [])) 
             by <_,_> isEven? isSumEven?)
disj2 = Pass

disj3 : runVerbose (Test (Property (Even 1)) ∨ Not (Property (Even 0)) 
                   on ([] , [])
                   by (isEven? 1 , isEven? 0))
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
                   by <_,_> isEven? isNextEven?)
impl2 = Failed (Test.∃ ⟨ 0 ⟩ (Hold (Even 0) And DoesNotHold (Even 1)))

impl3 : runVerbose (Test Forall n ~ (Property (Even n)) ⇒ Property (Even (n + 2))
        on (odds nats) ∷ ([] , [])
        by <_,_> isEven? (λ n -> isEven? (n + 2)))
impl3 = Pass (ForAll ℕ (Fst ✗))

conj1 : runVerbose (Test Exists! n ~ (Property (Even n)) ∧ Property (n + n ≡ n)
        on nats ∷ ([] , [])
        by ( <_,_> isEven? (λ n → n + n ≟ n)))
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

-- Since double implication is defined using conjunction we can't help to repeat
-- both input values and decision functions (even if they are the same)
iff1 : run (Test Forall n ~ (Property (Even n)) ⇔ (Not (Property (Even (n + 1))))
            on nats ∷ (([] , []) , ([] , []))
            by <_,_> (<_,_> isEven? isNextEven?) ((<_,_> isNextEven? isEven?)) )
iff1 = Pass

iff1' : runVerbose (Test Forall n ~ (Property (Even n)) ⇔ (Not (Property (Even (n + 1))))
                    on nats ∷ (([] , []) , ([] , []))
                    by <_,_> (<_,_> isEven? isNextEven?) ((<_,_> isNextEven? isEven?)) )
iff1' = Pass (ForAll ℕ (Snd ✗ And Snd ✓))

iff2-fail : runVerbose (Test Forall n ~ (Property (Even n)) ⇔ (Property (Even (n + n)))
                        on nats ∷ (([] , []) , ([] , []))
                        by <_,_> (<_,_> isEven? isDoubleEven?) (<_,_> isDoubleEven? isEven?) )
iff2-fail = Failed (Test.∃ ⟨ 1 ⟩ (Snd (Hold (Even 2) And DoesNotHold (Even 1))))
