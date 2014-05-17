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

-- Returns the type of the view function required to check if 
-- the given property holds for some input values. 
⟦_⟧ : ∀ {xs} -> U xs -> Set
⟦ Forall {A = A} f ⟧ = (a : A) → ⟦ f a ⟧
⟦ Exists {A = A} f ⟧ = (a : A) → ⟦ f a ⟧
⟦ Property P ⟧ = Dec P


-- Contains input values for testing a property
data Input (F : Set -> Set) : (List Set) -> Set₁ where
  [] : Input F []
  _∷_ : ∀ {xs} {A : Set} -> F A -> Input F xs -> Input F (A ∷ xs)

infixr 5 _∷_ 

-- Shorthand
[_] : ∀ {F A} -> F A -> Input F (A ∷ [])
[ x ] = x ∷ []

data Testable : Set₁ where
  Test_on_by_ : ∀ {A} -> (u : U A) -> Input List A -> (k : ⟦ u ⟧) -> Testable

mutual 
  data Result : Set₁ where
    RP : ResultP -> Result
    RA : Result∀ -> Result
    RE : Result∃ -> Result
  -- ...
  -- The possible results for a lemma with the ∀ quantifier
  data Result∀ : Set₁ where
    Forall : (A : Set) -> Result -> Result∀ 
    NotFor : {A : Set} -> A -> Result -> Result∀
    Trivial : Result∀ -- Empty set

  -- The possible results for a lemma with the ∃ quantifier
  data Result∃ : Set₁ where
    Exists : {A : Set} -> A -> Result -> Result∃
    NotExists : (A : Set) -> Result -> Result∃
    Impossible : Result∃

  -- The possible results for a property    -- TODO better names
  data ResultP : Set₁ where
    Hold : {P : Set} -> P -> ResultP
    DoesNotHold : {P : Set} -> ¬ P -> ResultP

open import Data.Sum

test : ∀ {xs} (u : U xs) -> ⟦ u ⟧ -> Input List xs -> Result ⊎ Result
test' : ∀ {xs} {A : Set} (u : U (A ∷ xs)) -> ⟦ u ⟧ -> List A -> Input List xs -> Result ⊎ Result

test' (Forall p) check [] input = inj₂ (RA Trivial)
test' (Forall p) check (x ∷ xs) input with test (p x) (check x) input
test' {A = A} (Forall p) check (x ∷ xs) input | inj₁ r = inj₁ (RA (NotFor x r))
test' {A = A} (Forall p) check (x ∷ []) input | inj₂ y = inj₂ (RA (Forall A y))
test' {A = A} (Forall p) check (x ∷ x₁ ∷ xs₁) input | inj₂ y = test' (Forall p) check (x₁ ∷ xs₁) input
test' (Exists p) check [] input = inj₁ (RE Impossible)
test' {A = A} (Exists p) check (x ∷ xs) input with test (p x) (check x) input 
test' {A = A} (Exists p) check (x ∷ []) input | inj₁ r = inj₁ (RE (NotExists A r))
test' {A = A} (Exists p) check (x ∷ x₁ ∷ xs) input | inj₁ r = test' (Exists p) check (x₁ ∷ xs) input
test' (Exists p) check (x ∷ xs) input | inj₂ r = inj₂ (RE (Exists x r)) 

test (Forall p) check (x ∷ input) = test' (Forall p) check x input
test (Exists p) check (x ∷ input) = test' (Exists p) check x input
test (Property P) (yes p) [] = inj₂ (RP (Hold p))
test (Property P) (no ¬p) [] = inj₁ (RP (DoesNotHold ¬p))

open import Data.Empty

data Fail : Result -> Set₁ where
  Failed : (r : Result) -> Fail r

data Succeed : Result -> Set₁ where
  Pass : (r : Result) -> Succeed r

-- TODO give precise result inspecting the outer quantifier
run : Testable -> Set₁
run (Test u on input by k) with test u k input
run (Test u on input by k) | inj₁ r = Fail r
run (Test u on input by k) | inj₂ r = Succeed r       -- TODO collect input

data Skip : Set where
  Skipped : Skip

-- Used to skip a test
skip : Testable -> Set
skip _ = Skip
