-- This module defines the data-type result, which describes the 
-- possible outcomes from testing a property

module Test.Result where

data Result : Set₁ where
-- The possible results for a lemma with the ∀ quantifier
   Forall : (A : Set) -> Result -> Result
   NotFor : {A : Set} -> A -> Result -> Result
   NotForall : (A : Set) -> Result -> Result
   Trivial : Result -- Empty set

-- The possible results for a lemma with the ∃ quantifier
   Exists : {A : Set} -> A -> Result -> Result
   Exists' : (A : Set) -> Result -> Result
   NotExists : (A : Set) -> Result -> Result
   Impossible : Result

-- The possible results for a lemma with the ∃! quantifier
   ExistsUnique : {A : Set} -> A -> Result -> Result
   NotUnique_~_&_~_ : {A : Set} -> A -> Result -> A -> Result -> Result

-- Disjunction
   _And_ : Result -> Result -> Result

-- The possible results for a property    -- TODO better names
   Hold : Set -> Result
   DoesNotHold : Set -> Result
   ✓ : Result
   ✗ : Result
