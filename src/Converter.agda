module Converter where

open import Base hiding ([_])

open import Reflection
open import Data.List
open import Data.Nat
open import Data.Unit

--------------------------------------------------------------------------------
-- Automatic conversion from lemmas to property universe
--------------------------------------------------------------------------------

-- Conversion error messages
data NotSupported : Term -> Set where
data UnsupportedSort : Sort -> Set where
data DontKnowRightNow : Term -> Set where

-- Constructor on the term level
property : Term -> Term
property p = con (quote Property) [ (arg visible relevant p) ]

forall' : Term -> Term -> Term -> Term
forall' ty blist next = con (quote Base.U.Forall) ((arg hidden relevant ty) ∷ (arg hidden relevant blist) ∷ ((arg visible relevant (lam visible next)) ∷ []))

bListTree[] : Term
bListTree[] = con (quote Base.BListTree.[]) []

bListTreeCons : Term -> Term -> Term
bListTreeCons x xs = con (quote Base.BListTree._∷_) ((arg visible relevant x) ∷ ((arg visible relevant xs) ∷ []))

-- | I don't know when should I stop checking
supportedT : Term -> Set
supportedT (var x args) = NotSupported (var x args)
supportedT (con c args) = DontKnowRightNow (con c args)
supportedT (def f args) = ⊤    -- Should I inspect args ?
supportedT (lam v t) = DontKnowRightNow (lam v t)
supportedT (pi t₁ (el s t)) = supportedT t
supportedT (sort x) = NotSupported (sort x)
supportedT unknown = NotSupported unknown

supported : Type -> Set
supported (el (set t) t₁) = UnsupportedSort (set t)
supported (el (lit zero) t) = supportedT t
supported (el (lit (suc n)) t) = UnsupportedSort (lit (suc n))
supported (el unknown t) = UnsupportedSort unknown

computeBListTree : (t : Term) -> {isSup : supportedT t} -> Term
computeBListTree (var x args) {}
computeBListTree (con c args) {}
computeBListTree (def f args) = bListTree[]
computeBListTree (lam v t) {}
computeBListTree (pi (arg v r (el s t)) (el s₁ t₁)) {isS} = bListTreeCons t (computeBListTree t₁ {isS})
computeBListTree (sort x) {}
computeBListTree unknown {}

-- TODO compute the index
convert : (t : Type) -> {isSup : supported t} -> Term
convertT : (t : Term) -> {isSup : supportedT t} -> Term

convertT (var x args) {}
-- Here I should check if c is ∃ (Exists) or ⊎ (∨) or (,) (∧) using primQNameEquality
-- In all the other cases it should fail (properties are types not values)
convertT (con c args) {}
convertT (def f args) = property (def f args) -- Property
convertT (lam v t) {}
convertT (pi (arg v r (el s ty)) (el s₁ t)) {isS} = forall' ty (computeBListTree t {isS}) (convertT t {isS})
convertT (sort x) {}
convertT unknown {}

convert (el (set t) t₁) {}
convert (el (lit zero) t) {isS} = convertT t {isS}
convert (el (lit (suc n)) t) {}
convert (el unknown t) {}

--------------------------------------------------------------------------------
-- Examples
--------------------------------------------------------------------------------

open import Data.Nat
open import Data.List

data Even  : ℕ → Set where
  isEven0  : Even 0
  isEven+2 : ∀ {n} → Even n → Even (suc (suc n))

f1 : U (ℕ ∷ [])
f1 = Forall n ~ Property (Even n)

-- quoteTerm f1
-- con Base.U.Forall
-- (arg hidden relevant (def Data.Nat.ℕ []) ∷
--  arg hidden relevant (con Base.BListTree.[] []) ∷
--  arg visible relevant
--  (lam visible
--   (con Base.U.Property
--    (arg visible relevant
--     (def Converter.Even (arg visible relevant (var 0 []) ∷ []))
--     ∷ [])))
--  ∷ [])

-- What I want (the signature of lemma) can be retrieved using 
--     type (quote lemma)
-- which produces 
-- el (lit 0)
-- (pi
--  (arg visible relevant
--   (el (lit 0) (def Data.Nat.ℕ .Data.List.List.[])))
--  (el (lit 0)
--   (def Converter.Even
--    (arg visible relevant (var 0 .Data.List.List.[]) .Data.List.List.∷
--     .Data.List.List.[]))))

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Sum
open import Data.Product

lemma1 : (n : ℕ) -> Even n
lemma1 = {!!}

lemma2 : (n : ℕ) -> (m : ℕ) -> Even (n + m)
lemma2 = {!!}

lemma3 : (n : ℕ) -> ¬ (Even n)
lemma3 = {!!}

lemma4 : (n : ℕ) -> (Even n) ⊎ (¬ (Even n))
lemma4 = {!!}

lemma5 : ∃ (λ n → Even n)
lemma5 = {!!}

test1 : unquote (convert (type (quote lemma1))) ≡ (Forall n ~ Property (Even n))
test1 = refl

test2 : unquote (convert (type (quote lemma2))) ≡ (Forall n ~ Forall m ~ (Property (Even (n + m))))
test2 = refl
