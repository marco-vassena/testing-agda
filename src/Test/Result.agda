-- This module defines the data-type result, which describes the 
-- possible outcomes from testing a property

module Test.Result where

open import Test.Base

data Result : BListTree Set -> Set₁ where
-- The possible results for a lemma with the ∀ quantifier
   Forall : ∀ {xs} (A : Set) -> Result xs -> Result (A ∷ xs)
   NotFor : ∀ {xs} {A : Set} -> A -> Result xs -> Result (A ∷ xs)
   Trivial : ∀ {xs} {A : Set} -> Result (A ∷ xs) -- Empty set

-- The possible results for a lemma with the ∃ quantifier
   Exists : ∀ {xs} {A : Set} -> A -> Result xs -> Result (A ∷ xs)
   NotExists : ∀ {xs} (A : Set) -> Result xs -> Result (A ∷ xs)
   Impossible : ∀ {xs} {A : Set} -> Result (A ∷ xs)

-- The possible results for a lemma with the ∃! quantifier
   ExistsUnique : ∀ {xs} {A : Set} -> A -> Result xs -> Result (A ∷ xs)
   NotUnique_~_&_~_ : ∀ {xs} {A : Set} -> A -> Result xs -> A -> Result xs -> Result (A ∷ xs)

-- Disjunction
   _And_ : ∀ {xs ys} -> Result xs -> Result ys -> Result (xs , ys)
   Fst : ∀ {xs ys} -> Result xs -> Result (xs , ys)
   Snd : ∀ {xs ys} -> Result ys -> Result (xs , ys)

-- The possible results for a property    -- TODO better names
   Hold : Set -> Result []
   DoesNotHold : Set -> Result []
