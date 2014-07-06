-- | This module allows to test properties using Streams as source of input values.

module Test.Input.Stream where

open import Test.Base
open import Test.Tester using (⟦_⟧ ; Testable)
open import Test.Input
import Test.Tester as T

open import Data.List hiding ( take )
open import Data.Stream hiding ( take )
open import Data.Vec hiding ( take )
open import Data.Nat
open import Function

-- | @take n xs@ takes the first @n@ elements of the given stream.
take : ∀ {a} -> ℕ -> Stream a -> List a
take {a} n = toList ∘ (Data.Stream.take {a} n)

-- | Transforms an Input Stream in an Input List taking the first n values. 
toInput : {xs : BListTree Set} -> ℕ -> Input Stream xs -> Input List xs
toInput n [] = []
toInput n (x ∷ input) = (take n x) ∷ (toInput n input)
toInput n (input1 , input2) = (toInput n input1) , (toInput n input2)

-- Tests up to a finite number of input values for each input type
Test_on_by_withℕ_ : ∀ {xs} -> (u : Predicate xs) -> Input Stream xs -> ⟦ u ⟧ -> ℕ -> Testable xs
Test_on_by_withℕ_ u input check n = T.Test u on (toInput n input) by check

-- Tests a property using a default number of input values (5)
Test_on_by_ : ∀ {xs} -> (u : Predicate xs) -> Input Stream xs -> ⟦ u ⟧ -> Testable xs
Test_on_by_ u input check = Test u on input by check withℕ 5
