-- This module defines the data-type result, which describes the 
-- possible outcomes from testing a property

module Test.Result where

import Test.Base as B
open import Test.Base using ( _∷_ ; _,_ ; [] )

data ValueOrSet : Set -> Set₁ where
  <_> : (A : Set) -> ValueOrSet A
  [_] : ∀ {A : Set} -> A -> ValueOrSet A

data Result : B.BListTree Set -> Set₁ where

   -- The possible results for a lemma with the ∀ quantifier  
   Forall : ∀ {xs} -> (A : Set) -> Result xs -> Result (A ∷ xs)
   Trivial : ∀ {xs} -> Result xs -- Empty set

   -- The possible results for a lemma with the ∃ quantifier
   Exists : ∀ {xs A} -> ValueOrSet A -> Result xs -> Result (A ∷ xs)
   NotExists : ∀ {xs} -> (A : Set) -> Result xs -> Result (A ∷ xs)
   Impossible : ∀ {xs} -> Result xs

   -- The possible results for a lemma with the ∃! quantifier
   ExistsUnique : ∀ {xs A} -> ValueOrSet A -> Result xs -> Result (A ∷ xs)
   NotUnique_~_&_~_ : ∀ {xs A} -> ValueOrSet A -> Result xs -> ValueOrSet A -> Result xs -> Result (A ∷ xs)

   -- Conjunction
   _And_ : ∀ {xs ys} -> Result xs  -> Result ys -> Result (xs , ys)
   Fst : ∀ {xs ys} -> Result xs -> Result (xs , ys)
   Snd : ∀ {xs ys} -> Result ys -> Result (xs , ys)

   -- The possible results for a property
   -- TODO better names
   Hold : Set -> Result []
   DoesNotHold : Set -> Result []
   ✓ : Result []
   ✗ : Result []

hide : ∀ {xs} -> B.Result xs -> Result xs
hide (B.Forall A r) = Forall A (hide r)
hide (B.NotFor x r) = Exists < _ > (hide r)
hide B.Trivial = Trivial
hide (B.Exists x r) = Exists < _ > (hide r)
hide (B.NotExists A r) = NotExists A (hide r)
hide B.Impossible = Impossible
hide (B.ExistsUnique x r) = ExistsUnique < _ > (hide r)
hide (B.NotUnique x ~ r1 & y ~ r2) = NotUnique < _ > ~ hide r1 & < _ > ~ hide r2
hide (r1 B.And r2) = (hide r1) And (hide r2)
hide (B.Fst r) = Fst (hide r)
hide (B.Snd r) = Snd (hide r)
hide (B.Hold x) = ✓
hide (B.DoesNotHold x) = ✗

normalize : ∀ {xs} -> B.Result xs -> Result xs
normalize (B.Forall A x) = hide (B.Forall A x)
normalize (B.NotFor x r) = Exists [ x ] (normalize r)
normalize B.Trivial = Trivial
normalize (B.Exists x r) = Exists [ x ] (normalize r)
normalize (B.NotExists A x) = hide (B.NotExists A x)
normalize B.Impossible = Impossible
normalize (B.ExistsUnique x r) = ExistsUnique [ x ] (normalize r)
normalize (B.NotUnique x ~ r1 & y ~ r2) = NotUnique [ x ] ~ normalize r1 & [ y ] ~ normalize r2
normalize (x B.And x₁) = normalize x And normalize x₁
normalize (B.Fst x) = Fst (normalize x)
normalize (B.Snd x) = Snd (normalize x)
normalize (B.Hold x) = Hold x
normalize (B.DoesNotHold x) = DoesNotHold x

--------------------------------------------------------------------------------
-- Auxiliary functions
--------------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality hiding ( [_] )
open import Relation.Binary
open import Relation.Nullary
open import Relation.Binary.HeterogeneousEquality
open import Data.Empty


_≟-ValueOrSet_ : {A : Set} {dec : Decidable (_≡_ {A = A}) } -> Decidable (_≡_ {A = ValueOrSet A})
_≟-ValueOrSet_ {A} < .A > < .A > = yes refl
_≟-ValueOrSet_ {A} < .A > ValueOrSet.[ x ] = no (λ ())
_≟-ValueOrSet_ {A} ValueOrSet.[ x ] < .A > = no (λ ())
_≟-ValueOrSet_ {dec = _≟_} ValueOrSet.[ x ] ValueOrSet.[ y ] with x ≟ y
ValueOrSet.[ .y ] ≟-ValueOrSet ValueOrSet.[ y ] | yes refl = yes refl
ValueOrSet.[ x ] ≟-ValueOrSet ValueOrSet.[ y ] | no ¬p = no (lemma ¬p)
  where lemma : ∀ {A} -> {x y : A} -> ¬ (x ≡ y) -> (ValueOrSet.[ x ] ≡ ValueOrSet.[ y ]) -> ⊥
        lemma p1 refl = p1 refl
