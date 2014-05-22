module Converter where

open import Reflection
open import Base

--------------------------------------------------------------------------------
-- Automatic conversion from lemmas to property universe
--------------------------------------------------------------------------------

-- Conversion error messages
data NotSupported : Term -> Set where
module Converter where

supportedT : Term -> Set
supportedT (var x args) = NotSupported (var x args)
supportedT (con c args) = {!!}
supportedT (def f args) = {!!}
supportedT (lam v t) = {!!}
supportedT (pi t₁ (el s t)) = supportedT t
supportedT (sort x) = NotSupported (sort x)
supportedT unknown = NotSupported unknown

supported : Type -> Set
supported (el (set t) t₁) = {!!}  -- Not sure here
supported (el (lit n) t) = supportedT t    -- Should it be only level 0 ?
supported (el unknown t) = NotSupported t


-- TODO compute the index
convert : (t : Type) -> {isSup : supported t} -> U {!!}
convertT : (t : Term) -> {isSup : supportedT t} -> U {!!}

convertT (var x args) {}
-- Here I should check if c is ∃ (Exists) or ⊎ (∨) or (,) (∧) using primQNameEquality
-- In all the other cases it should fail (properties are types not values)
convertT (con c args) = {!!}
convertT (def f args) = Property {!unquote (def f args)!}   -- How do I reconstruct the type?
convertT (lam v t) = {!!}
convertT (pi (arg v r (el s t)) t₂) = Forall {{!unquote t!}} (λ x → convert t₂)
convertT (sort x) {}
convertT unknown {}

convert (el (set t) t₁) = {!!}
convert (el (lit n) t) = convertT t
convert (el unknown t) {} 

--------------------------------------------------------------------------------
-- Examples
--------------------------------------------------------------------------------

open import Data.Nat
open import Data.List

data Even  : ℕ → Set where
  isEven0  : Even 0
  isEven+2 : ∀ {n} → Even n → Even (suc (suc n))

lemma : (n : ℕ) -> Even n
lemma n = {!!}

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
