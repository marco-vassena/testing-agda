module Test.Input.Generator.Base where

open import Coinduction
open import Data.Bool
open import Data.Nat
open import Data.Empty
open import Data.Unit
open import Data.Sum using (_⊎_)
open import Data.Product using (_×_ ; _,_)
open import Data.Colist using (Colist ; _∷_ ; [])
import Data.Colist as C
open import Function
open import Level as L

mutual

  data ColistP {ℓ} (A : Set ℓ) : Set (L.suc ℓ) where
    [] : ColistP A
    _∷_     : (x : A) (xs : ∞ (ColistP A)) → ColistP A
    zipWith : {B C : Set ℓ} (f : B → C → A)
              (xs : ColistP B) (ys : ColistP C) → ColistP A
    map     : {B : Set ℓ} (f : B → A) (xs : ColistP B) → ColistP A
    _++_ : ColistP A -> ColistP A -> ColistP A
    concatMap : {B : Set ℓ} -> (f : B -> ColistP A) -> {isP : IsProductive f} -> ColistP B -> ColistP A

  data ColistW {ℓ} (A : Set ℓ) : Set (L.suc ℓ) where
    [] : ColistW A
    _∷_ : (x : A) (xs : ColistP A) → ColistW A

  nonEmptyW : ∀ {ℓ} {A : Set ℓ} -> ColistW A -> Set
  nonEmptyW [] = ⊥
  nonEmptyW (x ∷ xs) = ⊤

  IsProductive : ∀ {ℓ} {A B : Set ℓ} -> (f : A -> ColistP B) -> Set ℓ 
  IsProductive {A = A} f = (a : A) -> nonEmptyW (whnf (f a))  -- Sound (but not complete) approximation of productive function

  whnf : ∀ {ℓ} {A : Set ℓ} → ColistP A → ColistW A
  whnf []                       = [] 
  whnf (x ∷ xs)                 = x ∷ ♭ xs
  whnf (zipWith f xs ys)        = zipWithW f (whnf xs) (whnf ys)
  whnf (map f xs)               = mapW f (whnf xs)
  whnf (xs ++ ys)               = (whnf xs) ++W (whnf ys)
  whnf (concatMap f {isP} xs)   = concatMapW f {isP} (whnf xs)

  zipWithW : ∀ {ℓ} {A B C : Set ℓ} →
             (A → B → C) → ColistW A → ColistW B → ColistW C
  zipWithW f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys
  zipWithW f _ _ = []

  mapW : ∀ {ℓ} {A B : Set ℓ} → (A → B) → ColistW A → ColistW B
  mapW f [] = []
  mapW f (x ∷ xs) = f x ∷ map f xs

  _++W_ : ∀ {ℓ} {A : Set ℓ} -> ColistW A -> ColistW A -> ColistW A
  [] ++W ys = ys
  (x ∷ xs) ++W [] = x ∷ xs
  (x ∷ xs) ++W (y ∷ ys) = x ∷ (xs ++ (y ∷ (♯ ys)))

  concatMapW : ∀ {ℓ} {A B : Set ℓ} -> (f : A -> ColistP B) -> {isP : IsProductive f} -> ColistW A -> ColistW B
  concatMapW f [] = []
  concatMapW f {isP} (x ∷ xs) with whnf (f x) | isP x
  concatMapW f {isP} (x ∷ xs) | [] | ()
  concatMapW f {isP} (x ∷ xs) | y ∷ ys | tt = y ∷ (ys ++ (concatMap f {isP} xs))

mutual
  ⟦_⟧W : ∀ {ℓ} {A : Set ℓ} → ColistW A → Colist A
  ⟦ x ∷ xs ⟧W = x ∷ ♯ ⟦ xs ⟧P
  ⟦ [] ⟧W = []

  ⟦_⟧P : ∀ {ℓ} {A : Set ℓ} → ColistP A → Colist A
  ⟦ xs ⟧P = ⟦ whnf xs ⟧W

fromColist : ∀ {ℓ} {A : Set ℓ} -> Colist A -> ColistP A
fromColist [] = []
fromColist (x ∷ xs) = x ∷ (♯ (fromColist (♭ xs)))

open import Data.List using (List ; _∷_ ; [])

fromList :  ∀ {ℓ} {A : Set ℓ} -> List A -> ColistP A
fromList [] = []
fromList (x ∷ xs) = x ∷ (♯ (fromList xs))

-- | Infinitely replicates the original non-empty colist.
cycle : ∀ {ℓ} {A : Set ℓ} -> (xs : ColistP A) -> {p : nonEmptyW (whnf xs)} -> ColistP A  
cycle xs {p} with whnf xs | p
cycle xs | [] | ()
cycle {A = A} xs {p} | y ∷ ys | tt = y ∷ ♯ (go (whnf ys))
  where go : ColistW A -> ColistP A
        go [] = cycle xs {p}
        go (z ∷ zs) = z ∷ ♯ (go (whnf zs))

iterate : ∀ {ℓ} {A : Set ℓ} -> (A -> A) -> A -> ColistP A
iterate f x = x ∷ ♯ (iterate f (f x))

-- f x y , ∀ x ∈ xs ∀ y ∈ ys
combine : ∀ {A B C : Set} -> (f : A -> B -> C) -> ColistP A -> ColistP B -> ColistP C
combine f xs ys with ⟦ ys ⟧P
combine f xs ys | [] = []
combine f xs _ | y ∷ ys = concatMap (λ x → map (f x) (fromColist (y ∷ ys))) xs

--------------------------------------------------------------------------------
-- Productive data types for Colist
--------------------------------------------------------------------------------

NonNull : ∀ {ℓ} {A : Set ℓ} -> Colist A -> Set
NonNull xs = T (not (C.null xs))

-- Productive data-type
data Prod {A B : Set} (f : A -> Colist B) : (xs : Colist A) -> Set₁ where
  Base : Prod f []
  Skip : {x : A} {xs : ∞ (Colist A)} -> Prod f (♭ xs) -> Prod f (x ∷ xs)
  Now : {x : A} {xs : ∞ (Colist A)} -> ∞ (Prod f (♭ xs)) -> NonNull (f x) -> Prod f (x ∷ xs)

concatMapC : ∀ {A B : Set} -> (f : A -> Colist B) -> (xs : Colist A) -> {isP : Prod f xs} -> Colist B
concatMapC f .[] {Base} = []
concatMapC f (x ∷ xs) {Skip isP} = concatMapC f (♭ xs) {isP}
concatMapC f (x ∷ xs) {Now isP nonNull} with f x
concatMapC f (x ∷ xs) {Now isP ()} | []
concatMapC {B = B} f (x ∷ xs) {Now isP tt} | y ∷ ys = unwrap y (♭ ys)
  where unwrap : B -> Colist B -> Colist B 
        unwrap z [] = z ∷ ♯ (concatMapC f (♭ xs) {♭ isP})
        unwrap z (z₁ ∷ zs) = z ∷ (♯ (unwrap z₁ (♭ zs)))

nonEmptyW2NonNull : ∀ {ℓ} {A : Set ℓ} -> {xs : ColistW A} -> nonEmptyW xs -> NonNull ⟦ xs ⟧W
nonEmptyW2NonNull {xs = []} ()
nonEmptyW2NonNull {xs = x ∷ xs} p = tt

-- Prod is as expressive as IsProductive (modulo ⟦_⟧P)
IsProductive2Prod : ∀ {A B} {f : A -> ColistP B} -> {xs : ColistP A} -> IsProductive f -> Prod (⟦_⟧P ∘ f) ⟦ xs ⟧P
IsProductive2Prod {xs = xs} p with whnf xs
IsProductive2Prod p | [] = Base
IsProductive2Prod {f = f} p | x ∷ xs with whnf (f x) | p x
IsProductive2Prod p | x ∷ xs | [] | ()
IsProductive2Prod {f = f} p | x ∷ xs | y ∷ ys | tt = Now (♯ (IsProductive2Prod {f = f} {xs = xs} p)) (nonEmptyW2NonNull (p x))
