module StreamGenerator where

open import Base hiding (Test_on_by_and_)
import Base as B
open import Data.List hiding ( take )
open import Data.Stream hiding ( take )
open import Data.Vec hiding (take)
open import Data.Nat
open import Function

take : ∀ {a} -> ℕ -> Stream a -> List a
take {a} n = toList ∘ (Data.Stream.take {a} n)

toInput : {xs : List Set} -> ℕ -> Input Stream xs -> Input List xs
toInput n [] = []
toInput n (x ∷ input) = (take n x) ∷ (toInput n input)

-- Tests up to n input values for each input type
Test_on_by_and_withℕ_ : ∀ {xs} -> (u : U xs) -> Input Stream xs -> ⟦ u ⟧ -> < u > -> ℕ -> Testable
Test_on_by_and_withℕ_ u input check prop n = B.Test u on (toInput n input) by check and prop

-- Provides default parameter (20)
Test_on_by_and_ : ∀ {xs} -> (u : U xs) -> Input Stream xs -> ⟦ u ⟧ -> < u > -> Testable
Test_on_by_and_ u input check prop = Test u on input by check and prop withℕ 5
