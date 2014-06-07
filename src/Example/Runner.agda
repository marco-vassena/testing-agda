-- Tests results using different runners

module Example.Runner where

open import Test.Base
open import Test.StreamGenerator
open import Test.Runner
open import Test.Tester using (Input ; [_])
open import Example.Even using (Even ; isEven? ; nats)

open import Data.Nat

double-even : pass (Test Forall n ~ Property (Even (n + n)) on [ nats ] 
                   by (λ n → isEven? (n + n)))
double-even = Pass

next-even : fail (Test Forall n ~ Property (Even (n + 1)) on [ nats ]
                 by (λ n → isEven? (n + 1)))
next-even = Pass
