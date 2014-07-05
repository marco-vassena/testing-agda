-- | Tests results using different runners

module Example.Runner where

open import Test.Base
open import Test.Input.Stream
open import Test.Runner
open import Test.Tester using (Input ; [_] ; Testable)
open import Test.Result
open import Example.Even using (Even ; isEven? ; nats)
open import Example.Simple using (impossible ; dec-impossible)


open import Data.Nat
open import Data.Empty
open import Data.Stream

double-even : pass (Test Forall n ~ Property (Even (n + n)) on [ nats ] 
                   by (λ n → isEven? (n + n)))
double-even = Pass

next-even : fail (Test Forall n ~ Property (Even (n + 1)) on [ nats ]
                 by (λ n → isEven? (n + 1)))
next-even = Pass

--------------------------------------------------------------------------------
-- fail_With_Using
--------------------------------------------------------------------------------

impossible-fail : fail (Test impossible on Test.Tester.[] by dec-impossible) With DoesNotHold ⊥ Using []
impossible-fail = Pass

-- | The real type wrapped in DoesNotHold and Hold is not really checked, so this test succeeds.
impossible-bug : fail (Test impossible on Test.Tester.[] by dec-impossible) With DoesNotHold (Even 2) Using []
impossible-bug = Pass

test-all-even : Stream ℕ -> Testable (ℕ ∷ [])
test-all-even xs = Test (Forall n ~ Property (Even n)) on [ xs ] by isEven?

all-even-pass : fail (test-all-even nats)
                 With ∃ ⟨ 1 ⟩ (DoesNotHold (Even 1)) 
                 Using (_≟_ ∷ [])
all-even-pass = Pass

all-even-fail : fail (test-all-even nats)
                 With ∃ ⟨ 2 ⟩ (DoesNotHold (Even 2)) 
                 Using (_≟_ ∷ [])
all-even-fail = Expected (∃ ⟨ 2 ⟩ (DoesNotHold (Even 2))) Got (∃ ⟨ 1 ⟩ (DoesNotHold (Even 1))) 

all-even-fail2 : fail (test-all-even (evens nats))
                 With ∃ ⟨ 1 ⟩ (DoesNotHold (Even 1)) 
                 Using (_≟_ ∷ [])
all-even-fail2 = Failed (ForAll ℕ ✓)
