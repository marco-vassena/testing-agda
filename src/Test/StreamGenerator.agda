-- TODO module Test.Generator ?
-- TODO name InputStream

-- | This module allows to test properties using
-- Streams as source of input values.

module Test.StreamGenerator where

open import Test.Base
open import Test.Tester using (Input ; [] ; _∷_ ; _,_ ; ⟦_⟧ ; Testable)
import Test.Tester as T

open import Data.List hiding ( take )
open import Data.Stream hiding ( take )
open import Data.Vec hiding ( take )
open import Data.Nat
open import Function

take : ∀ {a} -> ℕ -> Stream a -> List a
take {a} n = toList ∘ (Data.Stream.take {a} n)

toInput : {xs : BListTree Set} -> ℕ -> Input Stream xs -> Input List xs
toInput n [] = []
toInput n (x ∷ input) = (take n x) ∷ (toInput n input)
toInput n (input1 , input2) = (toInput n input1) , (toInput n input2)

-- Tests up to n input values for each input type
Test_on_by_withℕ_ : ∀ {xs} -> (u : U xs) -> Input Stream xs -> ⟦ u ⟧ -> ℕ -> Testable
Test_on_by_withℕ_ u input check n = T.Test u on (toInput n input) by check

-- Provides default parameter (5)
Test_on_by_ : ∀ {xs} -> (u : U xs) -> Input Stream xs -> ⟦ u ⟧ -> Testable
Test_on_by_ u input check = Test u on input by check withℕ 5
