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

forall' : Term -> Term -> Term
forall' ty next = con (quote Base.U.Forall) (argTy ∷ argNext ∷ [])
  where argTy = arg hidden relevant ty
        argNext = arg visible relevant (lam visible next)

not : Term -> Term
not next = con (quote Base.U.Not) (argNext ∷ [])
  where argNext = arg visible relevant next

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

convertTerm : (t : Term) -> {isSup : supportedTerm t} -> Term
convertTerm (var x args) {}
convertTerm (con c args) {}
convertTerm (def f args) {isS} = property (def f args)
convertTerm (lam v t) {}
convertTerm (pi (arg v r (el s ty)) (el s₁ t)) {isS} = forall' ty (convertTerm t {isS})
convertTerm (sort x) {}
convertTerm unknown {}

convert : (name : Name) -> {isSup : supported (type name)} -> Term
convert n {isSup} with type n
convert n {} | el (set t) t₁
convert n {isSup} | el (lit zero) t = convertTerm t {isSup}
convert n {} | el (lit (suc n₁)) t 
convert n {} | el unknown t
