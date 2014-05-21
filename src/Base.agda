module Base where

open import Coinduction
open import Data.Bool
open import Data.Nat
open import Data.List hiding ( [_] )
open import Reflection
open import Relation.Nullary
open import Function
 
-- Specific Results chosen based on the outmost quantifier.

-- data Pass : Set where
--   Ok : Pass

-- Property falsifiable for an input
data ¬_for_ {Input : Set} (Property : Set) : Input -> Set where
  CounterExample : (x : Input) -> ¬ Property for x 

data NotFound : Set where

data _by_ {Input : Set} (Property : Set) : Input -> Set where
  Exists : (x : Input) -> Property by x

--------------------------------------------------------------------------------

-- Universe
data U : (List Set) -> Set₁ where
  Forall : {A : Set} -> ∀ {xs} -> (p : A -> U xs) -> U (A ∷ xs)
  Exists : {A : Set} -> ∀ {xs} -> (p : A -> U xs) -> U (A ∷ xs)
  Property : (P : Set) -> U []

syntax Exists (\x -> p) = Exists x ~ p     -- TODO find nice symbol for such that ( "." and ":" are reserved)
syntax Forall (\x -> p) = Forall x ~ p

-- Returns the type of the view function required to check if 
-- the given property holds for some input values. 
⟦_⟧ : ∀ {xs} -> U xs -> Set
⟦ Forall {A = A} f ⟧ = (a : A) → ⟦ f a ⟧
⟦ Exists {A = A} f ⟧ = (a : A) → ⟦ f a ⟧
⟦ Property P ⟧ = Dec P

-- Returns the type of the function required to report the property being test
<_> : ∀ {xs} -> U xs -> Set₁
< Forall {A = A} p > = (a : A) → < p a >
< Exists {A = A} p > = (a : A) → < p a >
-- The problem here is that the user can put any set, instead I would like it to be the type of the property 
-- being tested
< Property P > = Set 

-- Contains input values for testing a property
data Input (F : Set -> Set) : (List Set) -> Set₁ where
  [] : Input F []
  _∷_ : ∀ {xs} {A : Set} -> F A -> Input F xs -> Input F (A ∷ xs)

infixr 5 _∷_ 

-- Shorthand
[_] : ∀ {F A} -> F A -> Input F (A ∷ [])
[ x ] = x ∷ []

data Testable : Set₁ where
  Test_on_by_and_ : ∀ {A} -> (u : U A) -> Input List A -> (k : ⟦ u ⟧) -> (prop : < u >) -> Testable

data Result : Set₁ where
-- The possible results for a lemma with the ∀ quantifier
   Forall : (A : Set) -> Result -> Result
   NotFor : {A : Set} -> A -> Result -> Result
   Trivial : Result -- Empty set

-- The possible results for a lemma with the ∃ quantifier
   Exists : {A : Set} -> A -> Result -> Result
   NotExists : (A : Set) -> Result -> Result
   Impossible : Result

-- The possible results for a property    -- TODO better names
   Hold : Set -> Result
   DoesNotHold : Set -> Result
  -- ...

open import Data.Sum

test : ∀ {xs} (u : U xs) -> ⟦ u ⟧ -> < u > -> Input List xs -> Result ⊎ Result
test' : ∀ {xs} {A : Set} (u : U (A ∷ xs)) -> ⟦ u ⟧ -> < u > -> List A -> Input List xs -> Result ⊎ Result

test' (Forall p) check prop [] input = inj₂ Trivial
test' (Forall p) check prop (x ∷ xs) input with test (p x) (check x) (prop x) input
test' {A = A} (Forall p) check prop (x ∷ xs) input | inj₁ r = inj₁ (NotFor x r)
test' {A = A} (Forall p) check prop (x ∷ []) input | inj₂ y = inj₂ (Forall A y)
test' {A = A} (Forall p) check prop (x ∷ x₁ ∷ xs₁) input | inj₂ y = test' (Forall p) check prop (x₁ ∷ xs₁) input
test' (Exists p) check prop [] input = inj₁ Impossible
test' {A = A} (Exists p) check prop (x ∷ xs) input with test (p x) (check x) (prop x) input 
test' {A = A} (Exists p) check prop (x ∷ []) input | inj₁ r = inj₁ (NotExists A r)
test' {A = A} (Exists p) check prop (x ∷ x₁ ∷ xs) input | inj₁ r = test' (Exists p) check prop (x₁ ∷ xs) input
test' (Exists p) check prop (x ∷ xs) input | inj₂ r = inj₂ (Exists x r)

test (Forall p) check prop (x ∷ input) = test' (Forall p) check prop x input
test (Exists p) check prop (x ∷ input) = test' (Exists p) check prop x input
test (Property P) (yes p) prop [] = inj₂ (Hold prop)
test (Property P) (no ¬p) prop [] = inj₁ (DoesNotHold prop)

open import Data.Empty

data Fail : Result -> Set₁ where
  Failed : (r : Result) -> Fail r

data Succeed : Result -> Set₁ where
  Pass : (r : Result) -> Succeed r

-- TODO give precise result inspecting the outer quantifier
run : Testable -> Set₁
run (Test u on input by k and prop) with test u k prop input
run (Test u on input by k and prop) | inj₁ r = Fail r
run (Test u on input by k and prop) | inj₂ r = Succeed r       -- TODO collect input

data Skip : Set where
  Skipped : Skip

-- Used to skip a test
skip : Testable -> Set
skip _ = Skip
