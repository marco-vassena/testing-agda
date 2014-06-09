module Converter where

open import Base hiding ([_])

open import Reflection
open import Data.List
open import Data.Nat
open import Data.Unit

--------------------------------------------------------------------------------
-- Term level constructor
--------------------------------------------------------------------------------

property : Term -> Term
property p = con (quote Property) [ argp ]
  where argp = arg visible relevant p

forall' : Term -> Term -> Term -> Term
forall' ty blist next = con (quote Base.U.Forall) (argTy ∷ argBList ∷ argNext ∷ [])
  where argTy = arg hidden relevant ty
        argBList = arg hidden relevant blist
        argNext = arg visible relevant (lam visible next)

not : Term -> Term
not next = con (quote Base.U.Not) (argNext ∷ [])
  where argNext = arg visible relevant next

bListTree[] : Term
bListTree[] = con (quote Base.BListTree.[]) []

bListTreeCons : Term -> Term -> Term
bListTreeCons x xs = con (quote Base.BListTree._∷_) ((arg visible relevant x) ∷ ((arg visible relevant xs) ∷ []))

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
open import Data.Empty


-- | TODO I have not found nothing like this in the standard library.
lookup : {A B : Set} -> {dec : Decidable {A = A} _≡_} -> A -> List (A × B) -> Maybe B
lookup a [] = nothing
lookup {dec = eq} a ((a' , b) ∷ xs) with eq a a'
lookup {dec = eq} .a ((a , b) ∷ xs) | yes refl = just b
lookup {dec = eq} a ((a' , b) ∷ xs) | no ¬p = lookup {dec = eq} a xs

-- | I don't know when should I stop checking
supportedTerm : Term -> Set
supportedTerm (var x args) = NotSupported (var x args)
supportedTerm (con c args) = DontKnowRightNow (con c args)
supportedTerm (def f args) = ⊤
supportedTerm (lam v t) = DontKnowRightNow (lam v t)
supportedTerm (pi t₁ (el s t)) = supportedTerm t  -- Should I call support (el s t) here ? 
supportedTerm (sort x) = NotSupported (sort x)
supportedTerm unknown = NotSupported unknown

supported : Type -> Set
supported (el (set t) t₁) = UnsupportedSort (set t)
supported (el (lit zero) t) = supportedTerm t
supported (el (lit (suc n)) t) = UnsupportedSort (lit (suc n))
supported (el unknown t) = UnsupportedSort unknown

computeBListTree : (t : Term) -> {isSup : supportedTerm t} -> Term
computeBListTree (var x args) {}
computeBListTree (con c args) {}
computeBListTree (def f args) = bListTree[]
computeBListTree (lam v t) {}
computeBListTree (pi (arg v r (el s t)) (el s₁ t₁)) {isS} = bListTreeCons t (computeBListTree t₁ {isS})
computeBListTree (sort x) {}
computeBListTree unknown {}

convertTerm : (t : Term) -> {isSup : supportedTerm t} -> Term

SpecialConverter : Set
SpecialConverter = (List (Arg Term)) -> Term

convert¬ : SpecialConverter
convert¬ (_ ∷ arg visible relevant x ∷ []) = not (convertTerm x)
convert¬ args = property (def (quote ¬_) args)

convert∃ : SpecialConverter
convert∃ args = {!!}

convert∧ : SpecialConverter
convert∧ args = {!!}

convert∨ : SpecialConverter
convert∨ args = {!!}

-- TODO ∃!
special-converter : List (Name × SpecialConverter)
special-converter = ((quote ¬_) , convert¬) ∷ (quote ∃ , convert∃) ∷ ((quote _×_) , convert∧) ∷ (quote _⊎_ , convert∨) ∷ []

convertTerm (var x args) {}
convertTerm (con c args) {}
convertTerm (def f args) {isS} with lookup {dec = _≟-Name_} f special-converter
convertTerm (def f args) | just converter = converter args
convertTerm (def f args) | nothing = property (def f args)
convertTerm (lam v t) {}
convertTerm (pi (arg v r (el s ty)) (el s₁ t)) {isS} = forall' ty (computeBListTree t {isS}) (convertTerm t {isS})
convertTerm (sort x) {}
convertTerm unknown {}

convert : (name : Name) -> {isSup : supported (type name)} -> Term
convert n {isSup} with type n
convert n {} | el (set t) t₁
convert n {isSup} | el (lit zero) t = convertTerm t {isSup}
convert n {} | el (lit (suc n₁)) t 
convert n {} | el unknown t
