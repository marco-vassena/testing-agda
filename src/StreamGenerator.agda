module StreamGenerator where

open import Base hiding (Test_on_by_)
import Base as B
open import Data.List hiding ( take )
open import Data.Stream hiding ( take )
open import Data.Vec hiding (take)
open import Data.Nat
open import Function

take : ∀ {a} -> ℕ -> Stream a -> List a
take {a} n = toList ∘ (Data.Stream.take {a} n)

toInput : {xs : List Set} -> ℕ -> Input Stream xs -> Input List xs
toInput n Nil = Nil
toInput n (Cons x input) = Cons (take n x) (toInput n input)

-- Tests up to n input values for each input type
Test_on_by_withℕ_ : ∀ {xs} -> (u : U xs) -> Input Stream xs -> ⟦ u ⟧ -> ℕ -> Testable
Test_on_by_withℕ_ u input check n = B.Test u on (toInput n input) by check

-- Provides default parameter (20)
Test_on_by_ : ∀ {xs} -> (u : U xs) -> Input Stream xs -> ⟦ u ⟧ -> Testable
Test_on_by_ u input check = Test u on input by check withℕ 20
