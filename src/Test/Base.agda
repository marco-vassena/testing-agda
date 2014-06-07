module Test.Base where

open import Data.Unit
open import Data.Empty
open import Data.Bool hiding (_∨_ ; _∧_)

-- Collect types for 'U'
data BListTree {a} (A : Set a) : Set a where 
  [] : BListTree A
  _∷_ : A -> BListTree A -> BListTree A
  _,_ : BListTree A -> BListTree A -> BListTree A

infixr 5 _∷_ 

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

syntax Exists (\x -> p) = Exists x ~ p
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
