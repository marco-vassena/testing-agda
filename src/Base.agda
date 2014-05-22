module Base where

open import Coinduction
open import Data.Unit
open import Data.Empty
open import Data.Bool hiding (_∨_ ; _∧_)
open import Data.Nat
open import Data.List hiding ( [_] )
open import Data.Product
open import Data.Sum
open import Reflection
open import Relation.Nullary
open import Function

--------------------------------------------------------------------------------
-- Definition of theorems and properties
--------------------------------------------------------------------------------

-- Collect types for 'U'
data BListTree {a} (A : Set a) : Set a where 
  [] : BListTree A
  _∷_ : A -> BListTree A -> BListTree A
  _,_ : BListTree A -> BListTree A -> BListTree A

-- Universe
data U : (BListTree Set) -> Set₁ where
  Forall : {A : Set} -> ∀ {xs} -> (p : A -> U xs) -> U (A ∷ xs)
  Exists : {A : Set} -> ∀ {xs} -> (p : A -> U xs) -> U (A ∷ xs)
  ExistsUnique : {A : Set} -> ∀ {xs} -> (p : A -> U xs) -> U (A ∷ xs)
  Not : ∀ {xs} -> U xs -> U xs
  _∨_ : ∀ {xs ys} -> U xs -> U ys -> U (xs , ys)
  Property : (P : Set) -> U []

-- Implication
_⇒_ : ∀ {xs ys} -> U xs -> U ys -> U (xs , ys)
p1 ⇒ p2 = (Not p1) ∨ p2

-- Conjunction
_∧_ : ∀ {xs ys} -> U xs -> U ys -> U (xs , ys)
p1 ∧ p2 = Not ((Not p1) ∨ (Not p2))

-- Double implication
-- TODO since it's not a primitive constructor I cannot help to repeat
-- the same functions (prop and check) twice. However they should always
-- be the same.
_⇔_ : ∀ {xs ys} -> U xs -> U ys -> U ((xs , ys) , (ys , xs))
p1 ⇔ p2 = (p1 ⇒ p2) ∧ (p2 ⇒ p1)

syntax Exists (\x -> p) = Exists x ~ p     -- TODO find nice symbol for such that ( "." and ":" are reserved)
syntax Forall (\x -> p) = Forall x ~ p
syntax ExistsUnique (\x -> p) = Exists! x ~ p

is∀ : ∀ {xs} -> U xs -> Set
is∀ (Forall p) = ⊤
is∀ _ = ⊥

is∃ : ∀ {xs} -> U xs -> Set
is∃ (Exists p) = ⊤
is∃ _ = ⊥

is∃! : ∀ {xs} -> U xs -> Set
is∃! (ExistsUnique p) = ⊤
is∃! _ = ⊥

--------------------------------------------------------------------------------
-- Testing framework
--------------------------------------------------------------------------------

-- Returns the type of the view function required to check if 
-- the given property holds for some input values. 
⟦_⟧ : ∀ {xs} -> U xs -> Set
⟦ Forall {A = A} f ⟧ = (a : A) → ⟦ f a ⟧
⟦ Exists {A = A} f ⟧ = (a : A) → ⟦ f a ⟧
⟦ ExistsUnique {A = A} f ⟧ = (a : A) → ⟦ f a ⟧
⟦ Not p ⟧ = ⟦ p ⟧
⟦ p1 ∨ p2 ⟧ = ⟦ p1 ⟧ × ⟦ p2 ⟧
⟦ Property P ⟧ = Dec P

-- Returns the type of the function required to report the property being test
<_> : ∀ {xs} -> U xs -> Set₁
< Forall {A = A} f > = (a : A) → < f a >
< Exists {A = A} f > = (a : A) → < f a >
< ExistsUnique {A = A} f > = (a : A) → < f a >
< Not p > = < p >
< p1 ∨ p2 > = < p1 > × < p2 >
-- The problem here is that the user can put any set, instead I would like it to be the type of the property 
-- being tested
< Property P > = Set 

-- Contains input values for testing a property
data Input (F : Set -> Set) : (BListTree Set) -> Set₁ where
  [] : Input F []
  _∷_ : ∀ {xs} {A : Set} -> F A -> Input F xs -> Input F (A ∷ xs)
  _,_ : ∀ {xs ys} -> Input F xs -> Input F ys -> Input F (xs , ys)

infixr 5 _∷_ 

-- Shorthand
[_] : ∀ {F A} -> F A -> Input F (A ∷ [])
[ x ] = x ∷ []

data Testable : Set₁ where
  Test_on_by_and_ : ∀ {xs} -> (u : U xs) -> Input List xs -> (k : ⟦ u ⟧) -> (prop : < u >) -> Testable

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


test : ∀ {xs} (u : U xs) -> ⟦ u ⟧ -> < u > -> Input List xs -> Result ⊎ Result
test∀ : ∀ {xs} {A : Set} (u : U (A ∷ xs)) {p : is∀ u} -> ⟦ u ⟧ -> < u > -> List A -> Input List xs -> Result ⊎ Result
test∃ : ∀ {xs} {A : Set} (u : U (A ∷ xs)) {p : is∃ u} -> ⟦ u ⟧ -> < u > -> List A -> Input List xs -> Result ⊎ Result
test∃! : ∀ {xs} {A : Set} (u : U (A ∷ xs)) {p : is∃! u} -> ⟦ u ⟧ -> < u > -> List A -> Input List xs -> Result ⊎ Result

test∀ (Forall p) check prop [] input = inj₂ Trivial
test∀ (Forall p) check prop (x ∷ xs) input with test (p x) (check x) (prop x) input
test∀ {A = A} (Forall p) check prop (x ∷ xs) input | inj₁ r = inj₁ (NotFor x r)
test∀ {A = A} (Forall p) check prop (x ∷ []) input | inj₂ y = inj₂ (Forall A y)
test∀ {A = A} (Forall p) check prop (x ∷ x₁ ∷ xs₁) input | inj₂ y = test∀ (Forall p) check prop (x₁ ∷ xs₁) input
test∀ (Exists p) {()} check prop xs₁ input
test∀ (ExistsUnique p) {()} check prop xs₁ input
test∀ (Not u) {()} check prop xs₁ input

test∃ (Exists p) check prop [] input = inj₁ Impossible
test∃ {A = A} (Exists p) check prop (x ∷ xs) input with test (p x) (check x) (prop x) input 
test∃ {A = A} (Exists p) check prop (x ∷ []) input | inj₁ r = inj₁ (NotExists A r)
test∃ {A = A} (Exists p) check prop (x ∷ x₁ ∷ xs) input | inj₁ r = test∃ (Exists p) check prop (x₁ ∷ xs) input
test∃ (Exists p) check prop (x ∷ xs) input | inj₂ r = inj₂ (Exists x r)
test∃ (ExistsUnique p) {()} check prop xs₁ input
test∃ (Forall p) {()} check prop xs₁ input
test∃ (Not u) {()} check prop xs₁ input


unique : ∀ {A xs} -> (p : A -> U xs) -> A -> Result -> ⟦ ExistsUnique p ⟧ -> < ExistsUnique p > ->
         List A -> Input List xs -> Result ⊎ Result
unique p x r check prop [] input = inj₂ (ExistsUnique x r)
unique p x r check prop (x₁ ∷ xs) input with test (p x₁) (check x₁) (prop x₁) input
unique p x r check prop (x₁ ∷ xs) input | inj₁ r2 = unique p x r check prop xs input
unique p x r check prop (x₂ ∷ xs) input | inj₂ r2 = inj₂ (NotUnique x ~ r & x₂ ~ r2)


test∃! (ExistsUnique p) {tt} check prop [] input = inj₁ Impossible
test∃! (ExistsUnique {A} p) {tt} check prop (x ∷ xs) input with test (p x) (check x) (prop x) input
test∃! (ExistsUnique {A} p) {tt} check prop (x ∷ []) input | inj₁ r = inj₁ (NotExists A r)
test∃! (ExistsUnique {A} p) {tt} check prop (x ∷ x₁ ∷ xs) input | inj₁ r = test∃! (ExistsUnique p) check prop (x₁ ∷ xs) input
test∃! (ExistsUnique {A} p) {tt} check prop (x ∷ xs) input | inj₂ r = unique p x r check prop xs input
test∃! (Forall p) {} check prop xs₁ input
test∃! (Exists p) {} check prop xs₁ input
test∃! (Not u) {} check prop xs₁ input

test (Forall p) check prop (x ∷ input) = test∀ (Forall p) check prop x input
test (Exists p) check prop (x ∷ input) = test∃ (Exists p) check prop x input
test (ExistsUnique p) check prop (x ∷ input) = test∃! (ExistsUnique p) check prop x input
test (Not p) check prop xs with test p check prop xs
test (Not p) check prop xs | inj₁ x = inj₂ x
test (Not p) check prop xs | inj₂ y = inj₁ y 
test (p1 ∨ p2) (check1 , check2) (prop1 , prop2) (input1 , input2) with test p1 check1 prop1 input1
test (p1 ∨ p2) (check1 , check2) (prop1 , prop2) (input1 , input2) | inj₁ x with test p2 check2 prop2 input2
test (p1 ∨ p2) (check1 , check2) (prop1 , prop2) (input1 , input2) | inj₁ r1 | inj₁ r2 = inj₁ (r1 And r2)
test (p1 ∨ p2) (check1 , check2) (prop1 , prop2) (input1 , input2) | inj₁ x | inj₂ y = inj₂ y
test (p1 ∨ p2) (check1 , check2) (prop1 , prop2) (input1 , input2) | inj₂ y = inj₂ y
test (Property P) (yes p) prop [] = inj₂ (Hold prop)
test (Property P) (no ¬p) prop [] = inj₁ (DoesNotHold prop)

data Fail : Result -> Set₁ where
  Failed : (r : Result) -> Fail r

data Succeed : Result -> Set₁ where
  Pass : (r : Result) -> Succeed r

-- TODO give precise result inspecting the outer quantifier
run : Testable -> Set₁
run (Test u on input by k and prop) with test u k prop input
run (Test u on input by k and prop) | inj₁ r = Fail r
run (Test u on input by k and prop) | inj₂ r = Succeed r

data Skip : Set where
  Skipped : Skip

-- Used to skip a test
skip : Testable -> Set
skip _ = Skip
