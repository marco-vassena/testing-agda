-- | Tests results using different runners

module Example.Runner where

open import Test.Base
open import Test.Input.Stream
open import Test.Runner
open import Test.Tester using ( [_] ; Testable ; ⟦_⟧)
open import Test.Input
open import Test.Result
open import Example.Even
open import Example.Simple using (impossible ; dec-impossible)


open import Data.Nat
open import Data.Empty
open import Data.Stream

pass-doubleEven : pass (Test doubleEven on [ nats ] by isDoubleEven?)
pass-doubleEven = Pass

nextEven : Predicate (ℕ ∷ [])
nextEven = Forall n ~ Property (Even (n + 1))

isNextEven? : ⟦ nextEven ⟧
isNextEven? n = isEven? (n + 1) 

fail-nextEven : fail (Test nextEven on [ nats ] by isNextEven?)
fail-nextEven = Pass

--------------------------------------------------------------------------------
-- fail_With_Using
--------------------------------------------------------------------------------

fail-impossible : fail (Test impossible on [] by dec-impossible) With DoesNotHold ⊥ Using []
fail-impossible = Pass

-- | The acutal type wrapped in DoesNotHold and Hold is not really checked, so this test succeeds.
-- It ought instead to fail complaining about how ⊥ is different from Even 2. Being those sets
-- it's not possible to compare them directly: only the type-checker can.
impossible-bug : fail (Test impossible on [] by dec-impossible) With DoesNotHold (Even 2) Using []
impossible-bug = Pass

-- Produces a testable with a given stream of input values
allEvenWith : Stream ℕ -> Testable (ℕ ∷ [])
allEvenWith xs = Test allEven on [ xs ] by isEven?

all-even-pass : fail (allEvenWith nats)
                 With ∃ ⟨ 1 ⟩ (DoesNotHold (Even 1)) 
                 Using (_≟_ ∷ [])
all-even-pass = Pass

all-even-fail : fail (allEvenWith nats)
                 With ∃ ⟨ 2 ⟩ (DoesNotHold (Even 2)) 
                 Using (_≟_ ∷ [])
all-even-fail = Expected (∃ ⟨ 2 ⟩ (DoesNotHold (Even 2))) Got (∃ ⟨ 1 ⟩ (DoesNotHold (Even 1))) 

all-even-fail2 : fail (allEvenWith (evens nats))
                 With ∃ ⟨ 1 ⟩ (DoesNotHold (Even 1)) 
                 Using (_≟_ ∷ [])
all-even-fail2 = Failed (ForAll ℕ ✓)
