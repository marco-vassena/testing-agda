-- | This modules defines different runners for 'Testable' objects and
-- the correspondent result data type.

module Test.Runner where

open import Test.Base using (BListTree ; [] ; _∷_ ; _,_)
open import Test.Result
open import Test.Tester

open import Data.Sum

--------------------------------------------------------------------------------
-- Test case results
--------------------------------------------------------------------------------

-- Simple version
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
  Expected_Got_ : ∀ {xs ys} -> (exp : Result xs) -> (act : Result ys) -> Expected exp Found act 

data Succeed₁ : Set₁ where
  Pass : Succeed₁

--------------------------------------------------------------------------------

-- | Returns a more informative description of the result of the test.
runVerbose : ∀ {xs} -> Testable xs -> Set₁
runVerbose (Test u on input by check) with test u check input
runVerbose (Test u on input by check) | inj₁ r = Fail: r
runVerbose (Test u on input by check) | inj₂ r = Succeed: r

-- Returns whether the test passed or failed
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

open import Data.Bool hiding (_≟_ ; _∧_)
import Data.Bool as B using ( _∧_ ; _∨_ )
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Reflection

data Comparator : BListTree Set -> Set₁ where
  [] : Comparator []
  _∷_ : ∀ {xs} {A : Set} -> ( _≟_ : Decidable (_≡_ {A = A}))  -> Comparator xs -> Comparator (A ∷ xs)
  _,_ : ∀ {xs ys} -> Comparator xs -> Comparator ys -> Comparator (xs , ys)

toBool : ∀ {p} {P : Set p} -> Dec P -> Bool
toBool (yes p₁) = true
toBool (no ¬p) = false

-- | Compares two 'Result's.
-- At the moment comparing the final property is a problem because there we have just a Set.
_==_by_ : ∀ {xs} -> (r1 : Result xs) -> (r2 : Result xs) -> Comparator xs -> Bool
ForAll A r1 == ForAll .A r2 by (_≟_ ∷ comp) = r1 == r2 by comp
Trivial == Trivial by comp = true
¬∃ A r1 == ¬∃ .A r2 by (_≟_ ∷ comp) = r1 == r2 by comp
∃ x r1 == ∃ y r2 by (_≟_ ∷ comp) = x≟y B.∧ r1 == r2 by comp
  where x≟y = toBool (_≟-ValueOrSet_ {dec = _≟_} x y)
Impossible == Impossible by comp = true
∃! x r1 == ∃! y r2 by (_≟_ ∷ comp) = x≟y B.∧ (r1 == r2 by comp) -- (toBool (x ≟ y))
  where x≟y = toBool (_≟-ValueOrSet_ {dec = _≟_} x y)
(NotUnique x1 ~ r1 & x2 ~ r2) == NotUnique y1 ~ r1' & y2 ~ r2' by (_≟_ ∷ comp) = values B.∧ results
  where x1≟y1 = toBool (_≟-ValueOrSet_ {dec = _≟_} x1 y1)
        x2≟y2 = toBool (_≟-ValueOrSet_ {dec = _≟_} x2 y2)
        values = x1≟y1 B.∧ x2≟y2
        results = r1 == r1' by comp B.∧ r2 == r2' by comp 
(r1 And r2) == (r1' And r2') by (comp1 , comp2) = (r1 == r1' by comp1 ) Data.Bool.∧ (r2 == r2' by comp2)
Fst r1 == Fst r2 by (comp , comp₁) = r1 == r2 by comp
Snd r1 == Snd r2 by (comp , comp₁) = r1 == r2 by comp₁
Hold x == Hold x₁ by comp = true
-- TODO do not allow Hold / DoesNotHold here but only ✓ and X
DoesNotHold x == DoesNotHold x₁ by comp = true -- TODO idem
✓ == ✓ by _ = true
✗ == ✗ by _ = true
_ == _ by _ = false

-- | The test will fail with the given result.
fail_With_Using_ : ∀ {xs} -> Testable xs -> Result xs -> Comparator xs -> Set₁
fail Test u on input by check With expected Using comp with test u check input 
fail Test u on input by check With expected Using comp | inj₁ actual with actual == expected by comp
fail Test u on input by check With expected Using comp | inj₁ actual | true = Succeed₁ 
fail Test u on input by check With expected Using comp | inj₁ actual | false = Expected expected Found actual
fail Test u on input by check With expected Using comp | inj₂ y = Fail: y

-- | The test will pass with the given result.
pass_With_Using_ : ∀ {xs} -> Testable xs -> Result xs -> Comparator xs -> Set₁
pass Test u on input by check With expected Using comp with test u check input 
pass Test u on input by check With expected Using comp | inj₂ actual with actual == expected by comp
pass Test u on input by check With expected Using comp | inj₂ actual | true = Succeed₁ 
pass Test u on input by check With expected Using comp | inj₂ actual | false = Expected expected Found actual
pass Test u on input by check With expected Using comp | inj₁ y = Fail: y
