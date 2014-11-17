module Test.Input.Base where

open import Test.Base

-- Container for the input values used to test a predicate.
-- The BListTree index, when shared with a Predicate, ensures
-- that the type of the values match the structure of the predicate. 
data Input (F : Set -> Set) : (BListTree Set) -> Set₁ where
  [] : Input F []
  _∷_ : ∀ {xs} {A : Set} -> F A -> Input F xs -> Input F (A ∷ xs)
  _,_ : ∀ {xs ys} -> Input F xs -> Input F ys -> Input F (xs , ys)

infixr 5 _∷_ 
