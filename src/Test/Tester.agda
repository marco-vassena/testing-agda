-- | This module represents  the  testing framework, in which 
-- predicates are unwrapped and tested agains the given input values
  
module Test.Tester where

open import Test.Base
open import Test.Input.Base

open import Data.List hiding ( [_] )
open import Data.Product
open import Data.Sum
open import Relation.Nullary

-- Shorthand
[_] : ∀ {F A} -> F A -> Input F (A ∷ [])
[ x ] = x ∷ []

-- Returns the type of the view function required to check if 
-- the given property holds for some input values. 
⟦_⟧ : ∀ {xs} -> Predicate xs -> Set
⟦ Forall {A = A} f ⟧ = (a : A) → ⟦ f a ⟧
⟦ Exists {A = A} f ⟧ = (a : A) → ⟦ f a ⟧
⟦ ExistsUnique {A = A} f ⟧ = (a : A) → ⟦ f a ⟧
⟦ Not p ⟧ = ⟦ p ⟧
⟦ p1 ∨ p2 ⟧ = ⟦ p1 ⟧ × ⟦ p2 ⟧
⟦ Property P ⟧ = Dec P

-- | It represents the minimal testable unit.
-- It collects what is needed to test a property
data Testable : (BListTree Set) -> Set₁ where
  Test_on_by_ : ∀ {xs} -> (u : Predicate xs) -> (input : Input List xs) -> (check : ⟦ u ⟧) -> Testable xs

open Internal

-- These functions test specific predicate constructs. They check that the semantics
-- of those constructs is reflected by the input values. The Result returned is tagged,
-- (left for failures, right for success). 
test' : ∀ {xs} (u : Predicate xs) -> ⟦ u ⟧ -> Input List xs -> Result xs ⊎ Result xs
test∀ : ∀ {xs} {A : Set} (u : Predicate (A ∷ xs)) {p : is∀ u} -> ⟦ u ⟧ -> List A -> Input List xs -> Result (A ∷ xs) ⊎ Result (A ∷ xs)
test∃ : ∀ {xs} {A : Set} (u : Predicate (A ∷ xs)) {p : is∃ u} -> ⟦ u ⟧ -> List A -> Input List xs -> Result (A ∷ xs) ⊎ Result (A ∷ xs)
test∃! : ∀ {xs} {A : Set} (u : Predicate (A ∷ xs)) {p : is∃! u} -> ⟦ u ⟧ -> List A -> Input List xs -> Result (A ∷ xs) ⊎ Result (A ∷ xs)

test∀ (Forall p) check [] input = inj₂ Trivial
test∀ (Forall p) check (x ∷ xs) input with test' (p x) (check x) input
test∀ {A = A} (Forall p) check (x ∷ xs) input | inj₁ r = inj₁ (NotFor x r)
test∀ {A = A} (Forall p) check (x ∷ []) input | inj₂ y = inj₂ (Forall A y)
test∀ {A = A} (Forall p) check (x ∷ x₁ ∷ xs₁) input | inj₂ y = test∀ (Forall p) check (x₁ ∷ xs₁) input
test∀ (Exists p) {()} check xs₁ input
test∀ (ExistsUnique p) {()} check xs₁ input
test∀ (Not u) {()} check xs₁ input

test∃ (Exists p) check [] input = inj₁ Impossible
test∃ {A = A} (Exists p) check (x ∷ xs) input with test' (p x) (check x) input 
test∃ {A = A} (Exists p) check (x ∷ []) input | inj₁ r = inj₁ (NotExists A r)
test∃ {A = A} (Exists p) check (x ∷ x₁ ∷ xs) input | inj₁ r = test∃ (Exists p) check (x₁ ∷ xs) input
test∃ (Exists p) check (x ∷ xs) input | inj₂ r = inj₂ (Exists x r)
test∃ (ExistsUnique p) {()} check xs₁ input
test∃ (Forall p) {()} check xs₁ input
test∃ (Not u) {()} check xs₁ input


unique : ∀ {A xs} -> (p : A -> Predicate xs) -> A -> Result xs -> ⟦ ExistsUnique p ⟧ ->
         List A -> Input List xs -> Result (A ∷ xs) ⊎ Result (A ∷ xs)
unique p x r check [] input = inj₂ (ExistsUnique x r)
unique p x r check (x₁ ∷ xs) input with test' (p x₁) (check x₁) input
unique p x r check (x₁ ∷ xs) input | inj₁ r2 = unique p x r check xs input
unique p x r check (x₂ ∷ xs) input | inj₂ r2 = inj₁ (NotUnique x ~ r & x₂ ~ r2)


test∃! (ExistsUnique p) {tt} check [] input = inj₁ Impossible
test∃! (ExistsUnique {A} p) {tt} check (x ∷ xs) input with test' (p x) (check x) input
test∃! (ExistsUnique {A} p) {tt} check (x ∷ []) input | inj₁ r = inj₁ (NotExists A r)
test∃! (ExistsUnique {A} p) {tt} check (x ∷ x₁ ∷ xs) input | inj₁ r = test∃! (ExistsUnique p) check (x₁ ∷ xs) input
test∃! (ExistsUnique {A} p) {tt} check (x ∷ xs) input | inj₂ r = unique p x r check xs input
test∃! (Forall p) {} check xs₁ input
test∃! (Exists p) {} check xs₁ input
test∃! (Not u) {} check xs₁ input

test' (Forall p) check (x ∷ input) = test∀ (Forall p) check x input
test' (Exists p) check (x ∷ input) = test∃ (Exists p) check x input
test' (ExistsUnique p) check (x ∷ input) = test∃! (ExistsUnique p) check x input
test' (Not p) check xs with test' p check xs
test' (Not p) check xs | inj₁ x = inj₂ x
test' (Not p) check xs | inj₂ y = inj₁ y 
test' (p1 ∨ p2) (check1 , check2) (input1 , input2) with test' p1 check1 input1
test' (p1 ∨ p2) (check1 , check2) (input1 , input2) | inj₁ x with test' p2 check2 input2
test' (p1 ∨ p2) (check1 , check2) (input1 , input2) | inj₁ r1 | inj₁ r2 = inj₁ (r1 And r2)
test' (p1 ∨ p2) (check1 , check2) (input1 , input2) | inj₁ x | inj₂ y = inj₂ (Snd y)
test' (p1 ∨ p2) (check1 , check2) (input1 , input2) | inj₂ y = inj₂ (Fst y)
test' (Property P) (yes p) [] = inj₂ (Hold P)
test' (Property P) (no ¬p) [] = inj₁ (DoesNotHold P)

open import Test.Result using (normalize)
import Test.Result as V

-- | Entry point of the testing framework.
-- Tests the predicate agains the input values and reports the normalized outcome.
test : ∀ {xs} (u : Predicate xs) -> ⟦ u ⟧ -> Input List xs -> V.Result xs ⊎ V.Result xs
test p check input with test' p check input
test p check input | inj₁ x = inj₁ (normalize x)
test p check input | inj₂ y = inj₂ (normalize y)
