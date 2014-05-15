module StreamGenerator where

open import Base using (U ; ⟦_⟧)
import Base as B
open import Data.List hiding ( take )
open import Data.Stream hiding ( take )
open import Data.Vec hiding (take)
open import Data.Nat
open import Function

take : ∀ {a} -> ℕ -> Stream a -> List a
take {a} n = toList ∘ (Data.Stream.take {a} n)

-- TODO can we reuse always the same input data type
data Input : (List Set) -> Set₁ where
  Nil : Input []
  Cons : ∀ {xs} {A : Set} -> Stream A -> Input xs -> Input (A ∷ xs)

toInput : {xs : List Set} -> ℕ -> Input xs -> B.Input xs
toInput n Nil = B.Nil
toInput n (Cons x input) = B.Cons (take n x) (toInput n input)

-- Tests up to n input values for each input type
Test_on_by_withℕ_ : ∀ {xs} -> (u : U xs) -> Input xs -> ⟦ u ⟧ -> ℕ -> B.Testable
Test_on_by_withℕ_ u input check n = B.Test u on (toInput n input) by check

-- Provides default parameter (20)
Test_on_by : ∀ {xs} -> (u : U xs) -> Input xs -> ⟦ u ⟧ -> B.Testable
Test_on_by u input check = Test u on input by check withℕ 20
