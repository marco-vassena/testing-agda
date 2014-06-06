module Base where

open import Coinduction
open import Data.Unit
open import Data.Empty
open import Data.Bool hiding (_∨_ ; _∧_)
open import Data.Nat
open import Data.List hiding ( [_] )
open import Data.Product
open import Data.Sum
open import Relation.Nullary
open import Function

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

-- Returns the type of the view function required to check if 
-- the given property holds for some input values. 
⟦_⟧ : ∀ {xs} -> U xs -> Set
⟦ Forall {A = A} f ⟧ = (a : A) → ⟦ f a ⟧
⟦ Exists {A = A} f ⟧ = (a : A) → ⟦ f a ⟧
⟦ ExistsUnique {A = A} f ⟧ = (a : A) → ⟦ f a ⟧
⟦ Not p ⟧ = ⟦ p ⟧
⟦ p1 ∨ p2 ⟧ = ⟦ p1 ⟧ × ⟦ p2 ⟧
⟦ Property P ⟧ = Dec P

is∀ : ∀ {xs} -> U xs -> Set
is∀ (Forall p) = ⊤
is∀ _ = ⊥

is∃ : ∀ {xs} -> U xs -> Set
is∃ (Exists p) = ⊤
is∃ _ = ⊥

is∃! : ∀ {xs} -> U xs -> Set
is∃! (ExistsUnique p) = ⊤
is∃! _ = ⊥

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

--------------------------------------------------------------------------------
-- Test case results
--------------------------------------------------------------------------------

-- Plain version
data Fail : Set₁ where
  Failed : Fail

data Succeed : Set₁ where
  Pass : Succeed

-- Verbose version
data Fail: : Result -> Set₁ where
  Failed : (r : Result) -> Fail: r

data Succeed: : Result -> Set₁ where
  Pass : (r : Result) -> Succeed: r

data Skip : Set where
  Skipped : Skip
--------------------------------------------------------------------------------

-- TODO give precise result inspecting the outer quantifier
runVerbose : Testable -> Set₁
runVerbose (Test u on input by check) with test u check input
runVerbose (Test u on input by check) | inj₁ r = Fail: r
runVerbose (Test u on input by check) | inj₂ r = Succeed: r

-- Returns only either passed or failed
run : Testable -> Set₁
run (Test u on input by check) with test u check input
run (Test u on input by check) | inj₁ _ = Fail
run (Test u on input by check) | inj₂ _ = Succeed

-- Used to skip a test
skip : Testable -> Set
skip _ = Skip

-- The test is expected to succeed
pass : Testable -> Set₁
pass (Test u on input by check) with test u check input
pass (Test u on input by check) | inj₁ x = Fail
pass (Test u on input by check) | inj₂ y = Succeed

-- The test is expected to fail
fail : Testable -> Set₁
fail (Test u on input by check) with test u check input
fail (Test u on input by check) | inj₁ x = Succeed
fail (Test u on input by check) | inj₂ y = Fail


-- TODO Is there some workaround to this?
-- I would like to write these runner in which the user not only specifies
-- whether the property should pass or fail, but also why, i.e. the expected
-- Result.
-- This requires decidable equality (≟) over Result
-- but since they it contains arbitrary Sets I don't think I can define that.

-- fail_With_ pass_With_ : Testable -> Result -> Set₁
