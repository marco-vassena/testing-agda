module Example where
{-
open import Test.Base
open import Test.Runner
open import Test.Tester hiding (Test_on_by_)
open import Test.StreamGenerator

open import Data.Nat
open import Data.Product as P hiding ( ∃ )
open import Data.List hiding (take ; [_] )
open import Relation.Binary.PropositionalEquality hiding ( [_] )
open import Relation.Nullary
-}

-- open import Example.Simple
-- open import Example.Even
-- open import Example.Runner
open import Example.Combinator

{-
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

--------------------------------------------------------------------------------
-- Pretty syntax
--------------------------------------------------------------------------------

test-pretty : U (ℕ ∷ [])
test-pretty = Forall n ~ (Property (n ≡ n))

test-pretty2 : U (ℕ ∷ List ℕ ∷ [])
test-pretty2 =  Forall n ~ Exists xs ~ (Property (n ≡ (length xs)))
-}
