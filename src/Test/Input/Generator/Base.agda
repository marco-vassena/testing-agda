module Test.Input.Generator.Base where

open import Coinduction
open import Data.Nat
open import Data.Empty
open import Data.Unit
open import Data.Sum using (_⊎_)
open import Data.Product using (_×_)
open import Data.Colist using (Colist ; _∷_ ; [])
open import Function

mutual

  data ColistP (A : Set) : Set1 where
    [] : ColistP A
    _∷_     : (x : A) (xs : ∞ (ColistP A)) → ColistP A
    zipWith : ∀ {B C} (f : B → C → A)
              (xs : ColistP B) (ys : ColistP C) → ColistP A
    map     : ∀ {B} (f : B → A) (xs : ColistP B) → ColistP A
    _++_ : ColistP A -> ColistP A -> ColistP A
    concatMap : ∀ {B} -> (f : B -> ColistP A) -> {isP : IsProductive f} -> ColistP B -> ColistP A

  data ColistW A : Set1 where
    [] : ColistW A
    _∷_ : (x : A) (xs : ColistP A) → ColistW A

  isConsW : ∀ {A} -> ColistW A -> Set
  isConsW [] = ⊥
  isConsW (x ∷ xs) = ⊤

  IsProductive : ∀ {A B : Set} -> (f : A -> ColistP B) -> Set
  IsProductive {A} f = (a : A) -> isConsW (whnf (f a))  -- Sound (but not complete) approximation of productive function

  whnf : ∀ {A} → ColistP A → ColistW A
  whnf []                       = [] 
  whnf (x ∷ xs)                 = x ∷ ♭ xs
  whnf (zipWith f xs ys)        = zipWithW f (whnf xs) (whnf ys)
  whnf (map f xs)               = mapW f (whnf xs)
  whnf (xs ++ ys)               = (whnf xs) ++W (whnf ys)
  whnf (concatMap f {isP} xs)   = concatMapW f {isP} (whnf xs)


  zipWithW : {A B C : Set} →
             (A → B → C) → ColistW A → ColistW B → ColistW C
  zipWithW f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys
  zipWithW f _ _ = []

  mapW : {A B : Set} → (A → B) → ColistW A → ColistW B
  mapW f [] = []
  mapW f (x ∷ xs) = f x ∷ map f xs

  _++W_ : {A : Set} -> ColistW A -> ColistW A -> ColistW A
  [] ++W ys = ys
  (x ∷ xs) ++W [] = x ∷ xs
  (x ∷ xs) ++W (y ∷ ys) = x ∷ (xs ++ (y ∷ (♯ ys)))

  concatMapW : {A B : Set} -> (f : A -> ColistP B) -> {isP : IsProductive f} -> ColistW A -> ColistW B
  concatMapW f [] = []
  concatMapW f {isP} (x ∷ xs) with whnf (f x) | isP x
  concatMapW f {isP} (x ∷ xs) | [] | ()
  concatMapW f {isP} (x ∷ xs) | y ∷ ys | tt = y ∷ (ys ++ (concatMap f {isP} xs))

mutual

  ⟦_⟧W : ∀ {A} → ColistW A → Colist A
  ⟦ x ∷ xs ⟧W = x ∷ ♯ ⟦ xs ⟧P
  ⟦ [] ⟧W = []

  ⟦_⟧P : ∀ {A} → ColistP A → Colist A
  ⟦ xs ⟧P = ⟦ whnf xs ⟧W

fromColist : ∀ {A} -> Colist A -> ColistP A
fromColist [] = []
fromColist (x ∷ xs) = x ∷ (♯ (fromColist (♭ xs)))
