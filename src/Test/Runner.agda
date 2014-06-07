-- | 
module Test.Runner where

open import Test.Base
open import Test.Tester

open import Data.Sum

--------------------------------------------------------------------------------
-- Test case results
--------------------------------------------------------------------------------

-- Plain version
data Fail : Set where
  Failed : Fail

data Succeed : Set where
  Pass : Succeed

-- Verbose version
data Fail: : Result -> Set₁ where
  Failed : (r : Result) -> Fail: r

data Succeed: : Result -> Set₁ where
  Pass : (r : Result) -> Succeed: r

data Skip : Set where
  Skipped : Skip

--------------------------------------------------------------------------------

-- TODO give precise result inspecting the outer quantifier
runVerbose : Testable -> Set₁
runVerbose (Test u on input by check) with test u check input
runVerbose (Test u on input by check) | inj₁ r = Fail: r
runVerbose (Test u on input by check) | inj₂ r = Succeed: r

-- Returns only either passed or failed
run : Testable -> Set
run (Test u on input by check) with test u check input
run (Test u on input by check) | inj₁ _ = Fail
run (Test u on input by check) | inj₂ _ = Succeed

-- Used to skip a test
skip : Testable -> Set
skip _ = Skip

-- The test is expected to succeed
pass : Testable -> Set
pass (Test u on input by check) with test u check input
pass (Test u on input by check) | inj₁ x = Fail
pass (Test u on input by check) | inj₂ y = Succeed

-- The test is expected to fail
fail : Testable -> Set
fail (Test u on input by check) with test u check input
fail (Test u on input by check) | inj₁ x = Succeed
fail (Test u on input by check) | inj₂ y = Fail


-- TODO Is there some workaround to this?
-- I would like to write these runner in which the user not only specifies
-- whether the property should pass or fail, but also why, i.e. the expected
-- Result.
-- This requires decidable equality (≟) over Result
-- but since they it contains arbitrary Sets I don't think I can define that.

-- fail_With_ pass_With_ : Testable -> Result -> Set₁
