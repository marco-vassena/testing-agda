-- | This module allows to test properties using Colists as source of input values.
-- This module is intended to be imported qualified.

module Test.Input.Colist where

open import Test.Base
open import Test.Tester using (⟦_⟧ ; Testable)
open import Test.Input
import Test.Tester as T

open import Data.Colist
import Data.Colist as C
open import Data.Nat
open import Data.List
import Data.BoundedVec.Inefficient as B
open import Function

-- | @take n xs@ takes the first @n@ elements of the given colist.
toList : {A : Set} -> ℕ -> Colist A -> List A
toList n = B.toList ∘ C.take n

-- | Transforms an Input Colist in an Input List taking the first n values. 
toInput : ∀ {xs} -> ℕ -> Input Colist xs -> Input List xs
toInput n [] = []
toInput n (x ∷ xs) = (toList n x) ∷ (toInput n xs)
toInput n (x₁ , x₂) = (toInput n x₁) , (toInput n x₂) 

-- Testable unit for colist up to a finite number of input values for each input type
Test_on_by_withℕ_ : ∀ {xs} -> (u : Predicate xs) -> Input Colist xs -> ⟦ u ⟧ -> ℕ -> Testable xs
Test_on_by_withℕ_ u input check n = T.Test u on (toInput n input) by check

-- Testable unit with colist using a default number of input values (5)
Test_on_by_ : ∀ {xs} -> (u : Predicate xs) -> Input Colist xs -> ⟦ u ⟧ -> Testable xs
Test_on_by_ u input check = Test u on input by check withℕ 5
