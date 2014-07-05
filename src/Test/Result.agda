-- This module defines the data-type Result, which describes the 
-- possible outcomes of testing a property

module Test.Result where

open import Test.Base

-- | Wrapper for either a value or a type.
data ValueOrSet : Set -> Set₁ where
  ⟨_⟩ : {A : Set} -> A -> ValueOrSet A
  <_> : (A : Set) -> ValueOrSet A

-- | User-exposed feedback for testing a predicate.
data Result : BListTree Set -> Set₁ where

   -- The possible results for a lemma with the ∀ quantifier  
   ForAll : ∀ {xs} -> (A : Set) -> Result xs -> Result (A ∷ xs)
   Trivial : ∀ {xs} -> Result xs -- Empty search space

   -- The possible results for a lemma with the ∃ quantifier
   ∃ : ∀ {xs A} -> ValueOrSet A -> Result xs -> Result (A ∷ xs)
   ¬∃ : ∀ {xs} -> (A : Set) -> Result xs -> Result (A ∷ xs)
   Impossible : ∀ {xs} -> Result xs -- Empty search space

   -- The possible results for a lemma with the ∃! quantifier
   ∃! : ∀ {xs A} -> ValueOrSet A -> Result xs -> Result (A ∷ xs)
   NotUnique_~_&_~_ : ∀ {xs A} -> ValueOrSet A -> Result xs -> ValueOrSet A -> Result xs -> Result (A ∷ xs)

   -- Conjunction
   _And_ : ∀ {xs ys} -> Result xs  -> Result ys -> Result (xs , ys)
   Fst : ∀ {xs ys} -> Result xs -> Result (xs , ys)
   Snd : ∀ {xs ys} -> Result ys -> Result (xs , ys)

   -- The possible results for a property
   Hold : Set -> Result []
   DoesNotHold : Set -> Result []
   ✓ : Result []
   ✗ : Result []

-- | Recursively hides specific partial results. It can be used to
-- report sensible feedback when universal quantification is involved.
hide : ∀ {xs} -> Internal.Result xs -> Result xs
hide (Internal.Forall A r) = ForAll A (hide r)
hide (Internal.NotFor x r) = ∃ < _ > (hide r)
hide Internal.Trivial = Trivial
hide (Internal.Exists x r) = ∃ < _ > (hide r)
hide (Internal.NotExists A r) = ¬∃ A (hide r)
hide Internal.Impossible = Impossible
hide (Internal.ExistsUnique x r) = ∃! < _ > (hide r)
hide (Internal.NotUnique x ~ r1 & y ~ r2) = NotUnique < _ > ~ hide r1 & < _ > ~ hide r2
hide (r1 Internal.And r2) = (hide r1) And (hide r2)
hide (Internal.Fst r) = Fst (hide r)
hide (Internal.Snd r) = Snd (hide r)
hide (Internal.Hold x) = ✓
hide (Internal.DoesNotHold x) = ✗

-- | Normalizes the result, hiding partial results when sensible.
normalize : ∀ {xs} -> Internal.Result xs -> Result xs
normalize (Internal.Forall A x) = hide (Internal.Forall A x)
normalize (Internal.NotFor x r) = ∃ ⟨ x ⟩ (normalize r)
normalize Internal.Trivial = Trivial
normalize (Internal.Exists x r) = ∃ ⟨ x ⟩ (normalize r)
normalize (Internal.NotExists A x) = hide (Internal.NotExists A x)
normalize Internal.Impossible = Impossible
normalize (Internal.ExistsUnique x r) = ∃! ⟨ x ⟩ (normalize r)
normalize (Internal.NotUnique x ~ r1 & y ~ r2) = NotUnique ⟨ x ⟩ ~ normalize r1 & ⟨ y ⟩ ~ normalize r2
normalize (x Internal.And x₁) = normalize x And normalize x₁
normalize (Internal.Fst x) = Fst (normalize x)
normalize (Internal.Snd x) = Snd (normalize x)
normalize (Internal.Hold x) = Hold x
normalize (Internal.DoesNotHold x) = DoesNotHold x

--------------------------------------------------------------------------------
-- Decidable equality over ValueOrSet
--------------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Relation.Nullary
open import Data.Empty

_≟-ValueOrSet_ : {A : Set} {dec : Decidable (_≡_ {A = A}) } -> Decidable (_≡_ {A = ValueOrSet A})
_≟-ValueOrSet_ {A} < .A > < .A > = yes refl
_≟-ValueOrSet_ {A} < .A > ⟨ x ⟩ = no (λ ())
_≟-ValueOrSet_ {A} ⟨ x ⟩ < .A > = no (λ ())
_≟-ValueOrSet_ {dec = _≟_} ⟨ x ⟩ ⟨ y ⟩ with x ≟ y
⟨ .y ⟩ ≟-ValueOrSet ⟨ y ⟩ | yes refl = yes refl
⟨ x ⟩ ≟-ValueOrSet ⟨ y ⟩ | no ¬p = no (lemma ¬p)
  where lemma : ∀ {A} -> {x y : A} -> ¬ (x ≡ y) -> (⟨ x ⟩ ≡ ⟨ y ⟩) -> ⊥
        lemma p1 refl = p1 refl
