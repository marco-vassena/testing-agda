-- | 
module Test.Runner where

open import Test.Base
open import Test.Tester
open import Test.Result

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
data Fail: : ∀ {xs} -> Result xs -> Set₁ where
  Failed : ∀ {xs} (r : Result xs) -> Fail: {xs} r

data Succeed: : ∀ {xs} -> Result xs -> Set₁ where
  Pass : ∀ {xs} (r : Result xs) -> Succeed: {xs} r

data Skip : Set where
  Skipped : Skip

-- | Expected / Actual result
data Expected_Found_ : ∀ {xs ys} -> Result xs -> Result ys -> Set₁ where
  Failed : ∀ {xs ys} -> (exp : Result xs) -> (act : Result ys) -> Expected exp Found act 

data Succeed₁ : Set₁ where
  Pass : Succeed₁

--------------------------------------------------------------------------------

-- TODO give precise result inspecting the outer quantifier
runVerbose : ∀ {xs} -> Testable xs -> Set₁
runVerbose (Test u on input by check) with test u check input
runVerbose (Test u on input by check) | inj₁ r = Fail: r
runVerbose (Test u on input by check) | inj₂ r = Succeed: r

-- Returns only either passed or failed
run : ∀ {xs} -> Testable xs -> Set
run (Test u on input by check) with test u check input
run (Test u on input by check) | inj₁ _ = Fail
run (Test u on input by check) | inj₂ _ = Succeed

-- Used to skip a test
skip : ∀ {xs} -> Testable xs -> Set
skip _ = Skip

-- The test is expected to succeed
pass : ∀ {xs} -> Testable xs -> Set
pass (Test u on input by check) with test u check input
pass (Test u on input by check) | inj₁ x = Fail
pass (Test u on input by check) | inj₂ y = Succeed

-- The test is expected to fail
fail : ∀ {xs} -> Testable xs -> Set
fail (Test u on input by check) with test u check input
fail (Test u on input by check) | inj₁ x = Succeed
fail (Test u on input by check) | inj₂ y = Fail


-- TODO Is there some workaround to this?
-- I would like to write these runner in which the user not only specifies
-- whether the property should pass or fail, but also why, i.e. the expected
-- Result.
-- This requires decidable equality (≟) over Result
-- but since they it contains arbitrary Sets I don't think I can define that.

open import Data.Bool

_==_ : ∀ {xs} -> (r1 : Result xs) -> (r2 : Result xs) -> Bool
Forall A r1 == Forall .A r2 = r1 == r2
NotFor x r1 == NotFor y r2 = {!!} -- equality on x y
Trivial == Trivial = true -- TODO this could be actually false, but we cannot distinguish it
Exists x r1 == Exists y r2 = {!!} -- equality on x y
NotExists A r1 == NotExists .A r2 = r1 == r2
Impossible == Impossible = {!!} -- TODO this could be actually false, but we cannot distinguish it
ExistsUnique x r1 == ExistsUnique x₁ r2 = {!!} -- equality
(NotUnique x ~ r1 & x₁ ~ r2) == (NotUnique x₂ ~ r3 & x₃ ~ r4) = {!!}
(r1 And r2) == (r1' And r2') = (r1 == r1') Data.Bool.∧ (r2 == r2')
Fst r1 == Fst r2 = r1 == r2
Snd r1 == Snd r2 = r1 == r2
Hold x == Hold x₁ = {!!}  -- TODO how do I enforce x and x₁ to be the same
DoesNotHold x == DoesNotHold x₁ = {!!} -- TODO idem
_ == _ = false

fail_With_ : ∀ {xs} -> Testable xs -> Result xs -> Set₁
fail Test u on input by check With expected with test u check input 
fail Test u on input by check With expected | inj₁ actual with actual == expected
fail Test u on input by check With expected | inj₁ actual | true = Succeed₁ 
fail Test u on input by check With expected | inj₁ actual | false = Expected expected Found actual
fail Test u on input by check With expected | inj₂ y = Fail: y
