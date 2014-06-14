module Converter where

open import Base hiding ([_] ; Test_on_by_and_)

open import Reflection
open import Data.List hiding (or ; and)
open import Data.Nat
open import Data.Unit
open import Data.Empty

--------------------------------------------------------------------------------
-- Term level constructor
--------------------------------------------------------------------------------

property : Term -> Term
property p = con (quote Property) [ argp ]
  where argp = arg visible relevant p

forall' : Term -> Term -> Term
forall' ty next = con (quote Base.U.Forall) (argTy ∷ argNext ∷ [])
  where argTy = arg hidden relevant ty
        argNext = arg visible relevant (lam visible next)

not : Term -> Term
not next = con (quote Base.U.Not) [ argNext ]
  where argNext = arg visible relevant next

or : Term -> Term -> Term
or t1 t2 = con (quote _∨_) (arg1 ∷ arg2 ∷ [])
  where arg1 = arg visible relevant t1
        arg2 = arg visible relevant t2

and : Term -> Term -> Term
and t1 t2 = def (quote _∧_) (arg1 ∷ arg2 ∷ [])
  where arg1 = arg visible relevant t1
        arg2 = arg visible relevant t2

exists : (t : Term) -> Term
exists t = con (quote Base.U.Exists) [ arg1 ]
  where arg1 = arg visible relevant (lam visible t)

--------------------------------------------------------------------------------
-- -- Conversion error messages
--------------------------------------------------------------------------------

data NotSupported : Term -> Set where
data UnsupportedSort : Sort -> Set where
data DontKnowRightNow : Term -> Set where

--------------------------------------------------------------------------------
-- Conversion of special constructs
--------------------------------------------------------------------------------

open import Data.Product
open import Relation.Nullary
open import Data.Sum
open import Data.Maybe
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Nat

-- | TODO I have not found nothing like this in the standard library.
lookup : {A B : Set} -> {dec : Decidable {A = A} _≡_} -> A -> List (A × B) -> Maybe B
lookup a [] = nothing
lookup {dec = eq} a ((a' , b) ∷ xs) with eq a a'
lookup {dec = eq} .a ((a , b) ∷ xs) | yes refl = just b
lookup {dec = eq} a ((a' , b) ∷ xs) | no ¬p = lookup {dec = eq} a xs

-- | The supported special constructs.
-- They have been defined explicitly as a data type because 
-- it's not possible to pattern match over a 'Name'.
data Special : Set where
  -- TODO ∃!
  Not : Special
  Or : Special
  And : Special
  Exists : Special

-- | Association list that maps specific 'Name's to their data type counterpart. 
name2Special : List (Name × Special)
name2Special = ((quote ¬_) , Not) ∷ (quote ∃ , Exists) ∷ ((quote _×_) , And) ∷ (quote _⊎_ , Or) ∷ []

supportedTerm : Term -> Set
supportedSpecial : Special -> List (Arg Term) -> Set

_is_And_ : Arg Term -> Visibility -> Relevance -> Set
arg v r t is v₁ And r₁ with v ≟-Visibility v₁ | r ≟-Relevance r₁
arg v r t is v₁ And r₁ | yes p | yes p₁ = supportedTerm t
arg v r t is v₁ And r₁ | yes p | no ¬p = ⊥
arg v r t is v₁ And r₁ | no ¬p | p2 = ⊥  

supportedSpecial Not (_ ∷ x ∷ []) = x is visible And relevant
supportedSpecial Not _ = ⊥
supportedSpecial Or (_ ∷ _ ∷ x₁ ∷ x₂ ∷ []) = x₁ is visible And relevant × x₂ is visible And relevant
supportedSpecial Or _ = ⊥
supportedSpecial And (_ ∷ _ ∷ x₁ ∷ x₂ ∷ []) = x₁ is visible And relevant × x₂ is visible And relevant
supportedSpecial And _ = ⊥
supportedSpecial Exists (_ ∷ _ ∷ _ ∷ x ∷ []) = x is visible And relevant
supportedSpecial Exists _ = ⊥

supportedTerm (var x args) = NotSupported (var x args)
supportedTerm (con c args) = DontKnowRightNow (con c args)
supportedTerm (def f args) with lookup {dec = _≟-Name_} f name2Special
supportedTerm (def f args) | just x = supportedSpecial x args
supportedTerm (def f args) | nothing = ⊤
supportedTerm (lam v t) = supportedTerm t
supportedTerm (pi t₁ (el s t)) = supportedTerm t 
supportedTerm (sort x) = NotSupported (sort x)
supportedTerm unknown = NotSupported unknown

supported : Type -> Set
supported (el s t) = supportedTerm t

convertTerm : (t : Term) -> {isSup : supportedTerm t} -> Term
convertSpecial : (s : Special) -> (args : List (Arg Term)) -> {isS : supportedSpecial s args} -> Term
convertArg : (a : Arg Term) -> (v : Visibility) -> (r : Relevance) -> {isS : a is v And r} -> Term

convertArg (arg v r t) v₁ r₁ {isS} with v ≟-Visibility v₁ | r ≟-Relevance r₁
convertArg (arg v r t) v₁ r₁ {isS} | yes p | yes p₁ = convertTerm t {isS}
convertArg (arg v r t) v₁ r₁ {} | yes p | no ¬p
convertArg (arg v r t) v₁ r₁ {} | no ¬p | p2

convertSpecial Not [] {}
convertSpecial Not (_ ∷ []) {}
convertSpecial Not (_ ∷ a ∷ []) {isS} = not (convertArg a visible relevant {isS})
convertSpecial Not (_ ∷ _ ∷ _ ∷ args) {} 
convertSpecial Or [] {}
convertSpecial Or (_ ∷ []) {}
convertSpecial Or (_ ∷ _ ∷ []) {}
convertSpecial Or (_ ∷ _ ∷ _ ∷ []) {}
convertSpecial Or (_ ∷ _ ∷ a₁ ∷ a₂ ∷ []) {isS₁ , isS₂} = or arg1 arg2
  where arg1 = convertArg a₁ visible relevant {isS₁}
        arg2 = convertArg a₂ visible relevant {isS₂}
convertSpecial Or (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ args) {}
convertSpecial And [] {}
convertSpecial And (_ ∷ []) {}
convertSpecial And (_ ∷ _ ∷ []) {}
convertSpecial And (_ ∷ _ ∷ _ ∷ []) {}
convertSpecial And (_ ∷ _ ∷ a₁ ∷ a₂ ∷ []) {isS₁ , isS₂} = and arg1 arg2
  where arg1 = convertArg a₁ visible relevant {isS₁}
        arg2 = convertArg a₂ visible relevant {isS₂}
convertSpecial And (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ args) {}
convertSpecial Exists [] {}
convertSpecial Exists (_ ∷ []) {}
convertSpecial Exists (_ ∷ _ ∷ []) {}
convertSpecial Exists (_ ∷ _ ∷ _ ∷ []) {}
convertSpecial Exists (_ ∷ _ ∷ _ ∷ a ∷ []) {isS} = exists (convertArg a visible relevant {isS})
convertSpecial Exists (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ args) {} 

convertTerm (var x args) {}
convertTerm (con c args) {}
convertTerm (def f args) {isS} with lookup {dec = _≟-Name_} f name2Special
convertTerm (def f args) {isS} | just x = convertSpecial x args {isS}
convertTerm (def f args) | nothing = property (def f args)
convertTerm (lam v t) {isS} = convertTerm t {isS}
convertTerm (pi (arg v r (el s ty)) (el s₁ t)) {isS} = forall' ty (convertTerm t {isS})
convertTerm (sort x) {}
convertTerm unknown {}

convert : (name : Name) -> {isSup : supported (type name)} -> Term
convert name {isS} with type name
convert name {isS} | el s t = convertTerm t {isS}
