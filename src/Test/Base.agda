module Test.Base where

open import Data.Unit
open import Data.Empty

-- Collect types for a predicate
data BListTree {a} (A : Set a) : Set a where 
  [] : BListTree A
  _∷_ : A -> BListTree A -> BListTree A
  _,_ : BListTree A -> BListTree A -> BListTree A

infixr 5 _∷_ 

-- Predicate Universe
data Predicate : (BListTree Set) -> Set₁ where
  Forall : {A : Set} -> ∀ {xs} -> (p : A -> Predicate xs) -> Predicate (A ∷ xs)
  Exists : {A : Set} -> ∀ {xs} -> (p : A -> Predicate xs) -> Predicate (A ∷ xs)
  ExistsUnique : {A : Set} -> ∀ {xs} -> (p : A -> Predicate xs) -> Predicate (A ∷ xs)
  Not : ∀ {xs} -> Predicate xs -> Predicate xs
  _∨_ : ∀ {xs ys} -> Predicate xs -> Predicate ys -> Predicate (xs , ys)
  Property : (P : Set) -> Predicate []

-- Implication
_⇒_ : ∀ {xs ys} -> Predicate xs -> Predicate ys -> Predicate (xs , ys)
p1 ⇒ p2 = (Not p1) ∨ p2

-- Conjunction
_∧_ : ∀ {xs ys} -> Predicate xs -> Predicate ys -> Predicate (xs , ys)
p1 ∧ p2 = Not ((Not p1) ∨ (Not p2))

-- Double implication
_⇔_ : ∀ {xs ys} -> Predicate xs -> Predicate ys -> Predicate ((xs , ys) , (ys , xs))
p1 ⇔ p2 = (p1 ⇒ p2) ∧ (p2 ⇒ p1)

syntax Exists (\x -> p) = Exists x ~ p
syntax Forall (\x -> p) = Forall x ~ p
syntax ExistsUnique (\x -> p) = Exists! x ~ p

is∀ : ∀ {xs} -> Predicate xs -> Set
is∀ (Forall p) = ⊤
is∀ _ = ⊥

is∃ : ∀ {xs} -> Predicate xs -> Set
is∃ (Exists p) = ⊤
is∃ _ = ⊥

is∃! : ∀ {xs} -> Predicate xs -> Set
is∃! (ExistsUnique p) = ⊤
is∃! _ = ⊥

module Internal where

  data Result : BListTree Set -> Set₁ where
    -- The possible results for a lemma with the ∀ quantifier
    Forall : ∀ {xs} (A : Set) -> Result xs -> Result (A ∷ xs)
    NotFor : ∀ {xs} {A : Set} -> A -> Result xs -> Result (A ∷ xs)
    Trivial : ∀ {xs} {A : Set} -> Result (A ∷ xs) -- Empty set

    -- The possible results for a lemma with the ∃ quantifier
    Exists : ∀ {xs} {A : Set} -> A -> Result xs -> Result (A ∷ xs)
    NotExists : ∀ {xs} (A : Set) -> Result xs -> Result (A ∷ xs)
    Impossible : ∀ {xs} {A : Set} -> Result (A ∷ xs)

    -- The possible results for a lemma with the ∃! quantifier
    ExistsUnique : ∀ {xs} {A : Set} -> A -> Result xs -> Result (A ∷ xs)
    NotUnique_~_&_~_ : ∀ {xs} {A : Set} -> A -> Result xs -> A -> Result xs -> Result (A ∷ xs)

    -- Disjunction
    _And_ : ∀ {xs ys} -> Result xs -> Result ys -> Result (xs , ys)
    Fst : ∀ {xs ys} -> Result xs -> Result (xs , ys)
    Snd : ∀ {xs ys} -> Result ys -> Result (xs , ys)

    -- The possible results for a property
    Hold : Set -> Result []
    DoesNotHold : Set -> Result []
