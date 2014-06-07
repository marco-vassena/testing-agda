-- | This module contains functions to test properties and data types to 
-- provide input values.
  
module Test.Tester where

open import Test.Base

open import Data.List hiding ( [_] )
open import Data.Product
open import Data.Sum
open import Relation.Nullary

-- Contains input values for testing a property
data Input (F : Set -> Set) : (BListTree Set) -> Set₁ where
  [] : Input F []
  _∷_ : ∀ {xs} {A : Set} -> F A -> Input F xs -> Input F (A ∷ xs)
  _,_ : ∀ {xs ys} -> Input F xs -> Input F ys -> Input F (xs , ys)

infixr 5 _∷_ 

-- Shorthand
[_] : ∀ {F A} -> F A -> Input F (A ∷ [])
[ x ] = x ∷ []

-- Returns the type of the view function required to check if 
-- the given property holds for some input values. 
⟦_⟧ : ∀ {xs} -> U xs -> Set
⟦ Forall {A = A} f ⟧ = (a : A) → ⟦ f a ⟧
⟦ Exists {A = A} f ⟧ = (a : A) → ⟦ f a ⟧
⟦ ExistsUnique {A = A} f ⟧ = (a : A) → ⟦ f a ⟧
⟦ Not p ⟧ = ⟦ p ⟧
⟦ p1 ∨ p2 ⟧ = ⟦ p1 ⟧ × ⟦ p2 ⟧
⟦ Property P ⟧ = Dec P

-- | Collects what is needed to test a property
data Testable : Set₁ where
  Test_on_by_ : ∀ {xs} -> (u : U xs) -> (input : Input List xs) -> (check : ⟦ u ⟧) -> Testable

data Result : Set₁ where
-- The possible results for a lemma with the ∀ quantifier
   Forall : (A : Set) -> Result -> Result
   NotFor : {A : Set} -> A -> Result -> Result
   Trivial : Result -- Empty set

-- The possible results for a lemma with the ∃ quantifier
   Exists : {A : Set} -> A -> Result -> Result
   NotExists : (A : Set) -> Result -> Result
   Impossible : Result

-- The possible results for a lemma with the ∃! quantifier
   ExistsUnique : {A : Set} -> A -> Result -> Result
   NotUnique_~_&_~_ : {A : Set} -> A -> Result -> A -> Result -> Result

-- Disjunction
   _And_ : Result -> Result -> Result

-- The possible results for a property    -- TODO better names
   Hold : Set -> Result
   DoesNotHold : Set -> Result

test : ∀ {xs} (u : U xs) -> ⟦ u ⟧ -> Input List xs -> Result ⊎ Result
test∀ : ∀ {xs} {A : Set} (u : U (A ∷ xs)) {p : is∀ u} -> ⟦ u ⟧ -> List A -> Input List xs -> Result ⊎ Result
test∃ : ∀ {xs} {A : Set} (u : U (A ∷ xs)) {p : is∃ u} -> ⟦ u ⟧ -> List A -> Input List xs -> Result ⊎ Result
test∃! : ∀ {xs} {A : Set} (u : U (A ∷ xs)) {p : is∃! u} -> ⟦ u ⟧ -> List A -> Input List xs -> Result ⊎ Result

test∀ (Forall p) check [] input = inj₂ Trivial
test∀ (Forall p) check (x ∷ xs) input with test (p x) (check x) input
test∀ {A = A} (Forall p) check (x ∷ xs) input | inj₁ r = inj₁ (NotFor x r)
test∀ {A = A} (Forall p) check (x ∷ []) input | inj₂ y = inj₂ (Forall A y)
test∀ {A = A} (Forall p) check (x ∷ x₁ ∷ xs₁) input | inj₂ y = test∀ (Forall p) check (x₁ ∷ xs₁) input
test∀ (Exists p) {()} check xs₁ input
test∀ (ExistsUnique p) {()} check xs₁ input
test∀ (Not u) {()} check xs₁ input

test∃ (Exists p) check [] input = inj₁ Impossible
test∃ {A = A} (Exists p) check (x ∷ xs) input with test (p x) (check x) input 
test∃ {A = A} (Exists p) check (x ∷ []) input | inj₁ r = inj₁ (NotExists A r)
test∃ {A = A} (Exists p) check (x ∷ x₁ ∷ xs) input | inj₁ r = test∃ (Exists p) check (x₁ ∷ xs) input
test∃ (Exists p) check (x ∷ xs) input | inj₂ r = inj₂ (Exists x r)
test∃ (ExistsUnique p) {()} check xs₁ input
test∃ (Forall p) {()} check xs₁ input
test∃ (Not u) {()} check xs₁ input


unique : ∀ {A xs} -> (p : A -> U xs) -> A -> Result -> ⟦ ExistsUnique p ⟧ ->
         List A -> Input List xs -> Result ⊎ Result
unique p x r check [] input = inj₂ (ExistsUnique x r)
unique p x r check (x₁ ∷ xs) input with test (p x₁) (check x₁) input
unique p x r check (x₁ ∷ xs) input | inj₁ r2 = unique p x r check xs input
unique p x r check (x₂ ∷ xs) input | inj₂ r2 = inj₁ (NotUnique x ~ r & x₂ ~ r2)


test∃! (ExistsUnique p) {tt} check [] input = inj₁ Impossible
test∃! (ExistsUnique {A} p) {tt} check (x ∷ xs) input with test (p x) (check x) input
test∃! (ExistsUnique {A} p) {tt} check (x ∷ []) input | inj₁ r = inj₁ (NotExists A r)
test∃! (ExistsUnique {A} p) {tt} check (x ∷ x₁ ∷ xs) input | inj₁ r = test∃! (ExistsUnique p) check (x₁ ∷ xs) input
test∃! (ExistsUnique {A} p) {tt} check (x ∷ xs) input | inj₂ r = unique p x r check xs input
test∃! (Forall p) {} check xs₁ input
test∃! (Exists p) {} check xs₁ input
test∃! (Not u) {} check xs₁ input

test (Forall p) check (x ∷ input) = test∀ (Forall p) check x input
test (Exists p) check (x ∷ input) = test∃ (Exists p) check x input
test (ExistsUnique p) check (x ∷ input) = test∃! (ExistsUnique p) check x input
test (Not p) check xs with test p check xs
test (Not p) check xs | inj₁ x = inj₂ x
test (Not p) check xs | inj₂ y = inj₁ y 
test (p1 ∨ p2) (check1 , check2) (input1 , input2) with test p1 check1 input1
test (p1 ∨ p2) (check1 , check2) (input1 , input2) | inj₁ x with test p2 check2 input2
test (p1 ∨ p2) (check1 , check2) (input1 , input2) | inj₁ r1 | inj₁ r2 = inj₁ (r1 And r2)
test (p1 ∨ p2) (check1 , check2) (input1 , input2) | inj₁ x | inj₂ y = inj₂ y
test (p1 ∨ p2) (check1 , check2) (input1 , input2) | inj₂ y = inj₂ y
test (Property P) (yes p) [] = inj₂ (Hold P)
test (Property P) (no ¬p) [] = inj₁ (DoesNotHold P)