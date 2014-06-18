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
data Testable : (BListTree Set) -> Set₁ where
  Test_on_by_ : ∀ {xs} -> (u : U xs) -> (input : Input List xs) -> (check : ⟦ u ⟧) -> Testable xs

test : ∀ {xs} (u : U xs) -> ⟦ u ⟧ -> Input List xs -> TaggedResult xs
test∀ : ∀ {xs} {A : Set} (u : U (A ∷ xs)) {p : is∀ u} -> ⟦ u ⟧ -> List A -> Input List xs -> TaggedResult (A ∷ xs)
test∃ : ∀ {xs} {A : Set} (u : U (A ∷ xs)) {p : is∃ u} -> ⟦ u ⟧ -> List A -> Input List xs -> TaggedResult (A ∷ xs)
test∃! : ∀ {xs} {A : Set} (u : U (A ∷ xs)) {p : is∃! u} -> ⟦ u ⟧ -> List A -> Input List xs -> TaggedResult (A ∷ xs)

test∀ (Forall p) check [] input = Pass Trivial
test∀ (Forall p) check (x ∷ xs) input with test (p x) (check x) input
test∀ {A = A} (Forall p) check (x ∷ xs) input | Fail r = Fail (NotFor x (Fail r))
test∀ {A = A} (Forall p) check (x ∷ []) input | Pass y = Pass (Forall A (Pass y))
test∀ {A = A} (Forall p) check (x ∷ x₁ ∷ xs₁) input | Pass y = test∀ (Forall p) check (x₁ ∷ xs₁) input
test∀ (Exists p) {()} check xs₁ input
test∀ (ExistsUnique p) {()} check xs₁ input
test∀ (Not u) {()} check xs₁ input

test∃ (Exists p) check [] input = Fail Impossible
test∃ {A = A} (Exists p) check (x ∷ xs) input with test (p x) (check x) input 
test∃ {A = A} (Exists p) check (x ∷ []) input | Fail r = Fail (NotExists A (Fail r))
test∃ {A = A} (Exists p) check (x ∷ x₁ ∷ xs) input | Fail r = test∃ (Exists p) check (x₁ ∷ xs) input
test∃ (Exists p) check (x ∷ xs) input | Pass r = Pass (Exists x (Pass r))
test∃ (ExistsUnique p) {()} check xs₁ input
test∃ (Forall p) {()} check xs₁ input
test∃ (Not u) {()} check xs₁ input


unique : ∀ {A xs} -> (p : A -> U xs) -> A -> TaggedResult xs -> ⟦ ExistsUnique p ⟧ ->
         List A -> Input List xs -> TaggedResult (A ∷ xs)
unique p x r check [] input = Pass (ExistsUnique x r)
unique p x r check (x₁ ∷ xs) input with test (p x₁) (check x₁) input
unique p x r check (x₁ ∷ xs) input | Fail r2 = unique p x r check xs input
unique p x r check (x₂ ∷ xs) input | Pass r2 = Fail (NotUnique x ~ r & x₂ ~ (Pass r2))


test∃! (ExistsUnique p) {tt} check [] input = Fail Impossible
test∃! (ExistsUnique {A} p) {tt} check (x ∷ xs) input with test (p x) (check x) input
test∃! (ExistsUnique {A} p) {tt} check (x ∷ []) input | Fail r = Fail (NotExists A (Fail r))
test∃! (ExistsUnique {A} p) {tt} check (x ∷ x₁ ∷ xs) input | Fail r = test∃! (ExistsUnique p) check (x₁ ∷ xs) input
test∃! (ExistsUnique {A} p) {tt} check (x ∷ xs) input | Pass r = unique p x (Pass r) check xs input
test∃! (Forall p) {} check xs₁ input
test∃! (Exists p) {} check xs₁ input
test∃! (Not u) {} check xs₁ input

test (Forall p) check (x ∷ input) = test∀ (Forall p) check x input
-- test (Forall p) check (x ∷ input) | inj₁ r = inj₁ r
-- test (Forall p) check (x ∷ input) | inj₂ r = inj₂ (hide r)
test (Exists p) check (x ∷ input) = test∃ (Exists p) check x input
-- test (Exists p) check (x ∷ input) | inj₁ r = inj₁ (hide r)
-- test (Exists p) check (x ∷ input) | inj₂ r = inj₂ r
test (ExistsUnique p) check (x ∷ input) = test∃! (ExistsUnique p) check x input
-- test (ExistsUnique p) check (x ∷ input) | inj₁ (NotUnique x₁ ~ x₂ & x₃ ~ x₄) = inj₁ (NotUnique x₁ ~ x₂ & x₃ ~ x₄)
-- test (ExistsUnique p) check (x ∷ input) | inj₁ r = inj₁ (hide r)
-- test (ExistsUnique p) check (x ∷ input) | inj₂ r = inj₂ r
test (Not p) check xs = test p check xs
-- test (Not p) check xs | inj₁ x = inj₂ x
-- test (Not p) check xs | inj₂ y = inj₁ y 
test (p1 ∨ p2) (check1 , check2) (input1 , input2) with test p1 check1 input1
test (p1 ∨ p2) (check1 , check2) (input1 , input2) | Fail x with test p2 check2 input2
test (p1 ∨ p2) (check1 , check2) (input1 , input2) | Fail r1 | Fail r2 = Fail ((Fail r1) And (Fail r2))
test (p1 ∨ p2) (check1 , check2) (input1 , input2) | Fail x | Pass y = Pass (Snd (Pass y))
test (p1 ∨ p2) (check1 , check2) (input1 , input2) | Pass y = Pass (Fst (Pass y))
test (Property P) (yes p) [] = Pass (Hold P)
test (Property P) (no ¬p) [] = Fail (DoesNotHold P)

data Result' : BListTree Set -> Set₁ where
  
  -- The possible results for a lemma with the ∀ quantifier
   Forall : ∀ {xs} -> (A : Set) -> Result' xs -> Result' (A ∷ xs)
   NotFor : ∀ {xs} -> {A : Set} -> A -> Result' xs -> Result' (A ∷ xs)
   NotForall : ∀ {xs} -> (A : Set) -> Result' xs -> Result' (A ∷ xs)
   Trivial : ∀ {xs} -> Result' xs -- Empty set

   -- The possible results for a lemma with the ∃ quantifier
   Exists : ∀ {xs} -> {A : Set} -> A -> Result' xs -> Result' (A ∷ xs)
   Exists' : ∀ {xs} -> (A : Set) -> Result' xs -> Result' (A ∷ xs)
   NotExists : ∀ {xs} -> (A : Set) -> Result' xs -> Result' (A ∷ xs)
   Impossible : ∀ {xs} -> Result' xs

   -- The possible results for a lemma with the ∃! quantifier
   ExistsUnique : ∀ {xs} {A : Set} -> A -> Result' xs -> Result' (A ∷ xs)
   ExistsUnique' : ∀ {xs} (A : Set) -> Result' xs -> Result' (A ∷ xs)

   NotUnique_~_&_~_ : ∀ {xs} {A : Set} -> A -> Result' xs -> A -> Result' xs -> Result' xs

-- -- Disjunction
--    _And_ : Result' -> Result' -> Result'

-- The possible results for a property    -- TODO better names
   Hold : Set -> Result' []
   DoesNotHold : Set -> Result' []
   ✓ : Result' []
   ✗ : Result' []

untag : ∀ {xs} -> TaggedResult xs -> Result xs
untag (Pass x) = x
untag (Fail x) = x

hide : ∀ {xs} -> TaggedResult xs -> Result' xs
hide r with untag r
hide r | Forall A x = Forall A (hide x)
hide r | NotFor {A = A} x r' = NotForall A (hide r')  -- TODO : Use Exists
hide r | Trivial = Trivial
hide r | Exists x r' = Exists' _ (hide r')
hide r | NotExists A x = NotExists A (hide x)
hide r | Impossible = Impossible
hide r | ExistsUnique x r' = ExistsUnique' _ (hide r')
hide r | NotUnique x ~ x₁ & x₂ ~ x₃ = {!!}
hide r | x And x₁ = {!!}
hide r | Fst x = {!!}
hide r | Snd x = {!!}
hide r | Hold x = ✓
hide r | DoesNotHold x = ✗

-- hide (Forall A r) = Forall A (hide r)
-- hide (NotFor {A} x r) = NotForall A (hide r)
-- hide (NotForall A r) = NotForall A (hide r)
-- hide Trivial = Trivial
-- hide (Exists {A} x r) = Exists' A (hide r)
-- hide (Exists' A r) = Exists' A (hide r)
-- hide (NotExists A r) = NotExists A (hide r)
-- hide Impossible = Impossible
-- hide (ExistsUnique x r) = ExistsUnique x (hide r)  -- Probably I need an ExistsUnique' also here
-- hide (NotUnique x ~ r & x₁ ~ r₁) = NotUnique x ~ hide r & x₁ ~ hide r₁
-- hide (r And r₁) = (hide r) And (hide r₁)
-- hide (Hold x) = ✓
-- hide (DoesNotHold x) = ✗
-- hide ✓ = ✓
-- hide ✗ = ✗

normalize : ∀ {xs} -> TaggedResult xs -> Result' xs
normalize (Pass (Forall A x)) = Forall A (hide x)
normalize (Pass (NotFor x r)) = NotFor x (normalize r)
normalize (Pass Trivial) = {!!}
normalize (Pass (Exists x x₁)) = {!!}
normalize (Pass (NotExists A x)) = {!!}
normalize (Pass Impossible) = {!!}
normalize (Pass (ExistsUnique x x₁)) = {!!}
normalize (Pass (NotUnique x ~ x₁ & x₂ ~ x₃)) = {!!}
normalize (Pass (x And x₁)) = {!!}
normalize (Pass (Fst x)) = {!!}
normalize (Pass (Snd x)) = {!!}
normalize (Pass (Hold x)) = Hold x
normalize (Pass (DoesNotHold x)) = DoesNotHold x
normalize (Fail x) = {!!}

test' : ∀ {xs} -> TaggedResult xs -> Result' xs ⊎ Result' xs
test' (Pass x) = inj₂ (normalize (Pass x))
test' (Fail x) = inj₁ (normalize (Fail x))

open import Data.Nat
data Even : ℕ -> Set where

example : TaggedResult (ℕ ∷ [])
example = Pass (Forall ℕ (Pass (Hold (Even 10))))
