-- | This module provides useful tools to write productive generators.
-- Part of this module is drawn from `Beating the Productivity Checker' 
-- `Mixing Induction and Coinduction' by Danielsson.

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

  -- | The language of colist programs 
  -- It contains common constructs used to manipulate colists. 
  data ColistP {ℓ} (A : Set ℓ) : Set (L.suc ℓ) where
    [] : ColistP A
    _∷_     : (x : A) (xs : ∞ (ColistP A)) → ColistP A
    zipWith : {B C : Set ℓ} (f : B → C → A)
              (xs : ColistP B) (ys : ColistP C) → ColistP A
    map     : {B : Set ℓ} (f : B → A) (xs : ColistP B) → ColistP A
    _++_ : ColistP A -> ColistP A -> ColistP A
    concatMap : {B : Set ℓ} -> (f : B -> ColistP A) -> {isP : IsProductive f} -> ColistP B -> ColistP A
    concatMap' : {B : Set ℓ} -> (f : B -> ColistP A) -> (xs : ColistP B) -> {isP : Prod' f (whnf xs)} -> ColistP A

  -- | A colist reduced to weak head normal form
  data ColistW {ℓ} (A : Set ℓ) : Set (L.suc ℓ) where
    [] : ColistW A
    _∷_ : (x : A) (xs : ColistP A) → ColistW A
  
  --------------------------------------------------------------------------------
  -- Productivity data type
  --------------------------------------------------------------------------------

  -- | Is a colist empty ? 
  nonEmptyW : ∀ {ℓ} {A : Set ℓ} -> ColistW A -> Set
  nonEmptyW [] = ⊥
  nonEmptyW (x ∷ xs) = ⊤

  -- | Defines a sound, but rather incomplete approximation of productive function
  IsProductive : ∀ {ℓ} {A B : Set ℓ} -> (f : A -> ColistP B) -> Set ℓ 
  IsProductive {A = A} f = (a : A) -> nonEmptyW (whnf (f a))

  -- | A proof data type that represents completely a productive function applied to a colist.
  data Prod' {ℓ} {A B : Set ℓ} (f : A -> ColistP B) : (xs : ColistW A) -> Set (L.suc ℓ) where
     Base : Prod' f []
     Skip : {x : A} {xs : (ColistP A)} -> Prod' f (whnf xs) -> Prod' f (x ∷ xs)
     Now : {x : A} {xs : (ColistP A)} -> ∞ (Prod' f (whnf  xs)) -> nonEmptyW (whnf (f x)) -> Prod' f (x ∷ xs)

  --------------------------------------------------------------------------------
  -- Semantics functions
  --------------------------------------------------------------------------------

  -- | Reduces a colist to weak head normal form 
  whnf : ∀ {ℓ} {A : Set ℓ} → ColistP A → ColistW A
  whnf []                       = [] 
  whnf (x ∷ xs)                 = x ∷ ♭ xs
  whnf (zipWith f xs ys)        = zipWithW f (whnf xs) (whnf ys)
  whnf (map f xs)               = mapW f (whnf xs)
  whnf (xs ++ ys)               = (whnf xs) ++W (whnf ys)
  whnf (concatMap f {isP} xs)   = concatMapW f {isP} (whnf xs)
  whnf (concatMap' f xs {isP})  = concatMapW' f (whnf xs) {isP}

  -- Semantics functions of the operators expressed in ColistP
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

  concatMapW' : ∀ {ℓ} {A B : Set ℓ} -> (f : A -> ColistP B) -> (xs : ColistW A) -> {isP : Prod' f xs} -> ColistW B
  concatMapW' f .[] {Base} = []
  concatMapW' f (x ∷ xs) {Skip isP} = concatMapW' f (whnf xs) {isP}
  concatMapW' f (x ∷ xs) {Now isP nonNull} with whnf (f x)
  concatMapW' f (x ∷ xs) {Now isP ()} | []
  concatMapW' f (x ∷ xs) {Now isP tt} | y ∷ ys = y ∷ (ys ++ concatMap' f xs {♭ isP})

mutual
  -- | Converter from a whnf colist to plain colist
  ⟦_⟧W : ∀ {ℓ} {A : Set ℓ} → ColistW A → Colist A
  ⟦ x ∷ xs ⟧W = x ∷ ♯ ⟦ xs ⟧P
  ⟦ [] ⟧W = []

  -- | Converter from a language of colist programs to plain colist
  ⟦_⟧P : ∀ {ℓ} {A : Set ℓ} → ColistP A → Colist A
  ⟦ xs ⟧P = ⟦ whnf xs ⟧W

-- | Converts a plain colist to the language of colist programs
fromColist : ∀ {ℓ} {A : Set ℓ} -> Colist A -> ColistP A
fromColist [] = []
fromColist (x ∷ xs) = x ∷ (♯ (fromColist (♭ xs)))

open import Data.List using (List ; _∷_ ; [])

-- | Converts a plain list to the language of colist programs
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

-- An infinite colist defined as :
-- iterate f x ≡ x ∷ f x ∷ f (f x) ∷ ...
iterate : ∀ {ℓ} {A : Set ℓ} -> (A -> A) -> A -> ColistP A
iterate f x = x ∷ ♯ (iterate f (f x))

-- f x y , ∀ x ∈ xs ∀ y ∈ ys
combine : ∀ {A B C : Set} -> (f : A -> B -> C) -> ColistP A -> ColistP B -> ColistP C
combine f xs ys with ⟦ ys ⟧P
combine f xs ys | [] = []
combine f xs _ | y ∷ ys = concatMap (λ x → map (f x) (fromColist (y ∷ ys))) xs

--------------------------------------------------------------------------------
-- Productive data types for standard Colist
--------------------------------------------------------------------------------

-- Is a colist non-empty?
NonNull : ∀ {ℓ} {A : Set ℓ} -> Colist A -> Set
NonNull xs = T (not (C.null xs))

-- Productive data-type
data Prod {ℓ} {A B : Set ℓ} (f : A -> Colist B) : (xs : Colist A) -> Set (L.suc ℓ) where
  Base : Prod f []
  Skip : {x : A} {xs : ∞ (Colist A)} -> Prod f (♭ xs) -> Prod f (x ∷ xs)
  Now : {x : A} {xs : ∞ (Colist A)} -> ∞ (Prod f (♭ xs)) -> NonNull (f x) -> Prod f (x ∷ xs)

-- | concatMap can be defined totally, given a productive proof
concatMapC : ∀ {ℓ} {A B : Set ℓ} -> (f : A -> Colist B) -> (xs : Colist A) -> {isP : Prod f xs} -> Colist B
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

-- Proof that Prod is as expressive as IsProductive (modulo ⟦_⟧P)
IsProductive2Prod : ∀ {ℓ} {A B : Set ℓ} {f : A -> ColistP B} -> {xs : ColistP A} -> IsProductive f -> Prod (⟦_⟧P ∘ f) ⟦ xs ⟧P
IsProductive2Prod {xs = xs} p with whnf xs
IsProductive2Prod p | [] = Base
IsProductive2Prod {f = f} p | x ∷ xs with whnf (f x) | p x
IsProductive2Prod p | x ∷ xs | [] | ()
IsProductive2Prod {f = f} p | x ∷ xs | y ∷ ys | tt = Now (♯ (IsProductive2Prod {f = f} {xs = xs} p)) (nonEmptyW2NonNull (p x))

IsProductive2Prod' : ∀ {ℓ} {A B : Set ℓ} {f : A -> ColistP B} -> {xs : ColistP A} -> IsProductive f -> Prod' f (whnf xs)
IsProductive2Prod' {xs = xs} p with whnf xs
IsProductive2Prod' p | [] = Base
IsProductive2Prod' {f = f} p | x ∷ xs₁ with whnf (f x) | p x
IsProductive2Prod' p | x ∷ xs | [] | ()
IsProductive2Prod' {f = f} p | x ∷ xs | y ∷ ys | tt = Now (♯ IsProductive2Prod' {f = f} {xs = xs} p) (p x)

--------------------------------------------------------------------------------
-- Self-generative colists
-- Proving the productiviy of self-referencing definitions such as
-- foo = 0 ∷ 1 ∷ concatMap' f foo
-- is usually very hard, due to the mutual dependency between the colist and the 
-- proof itself.
-- This section provides a simple, yet effective alternative that avoids the proof
-- burden completely, defining an appropriate total semantics also for looping
-- definitions.
--------------------------------------------------------------------------------

-- Self Generative data type.
-- Represents a colist obtained repeatedly mapping f over the input colist. 
data SG {ℓ} (A : Set ℓ) : (f : A -> ColistP A) -> Set (L.suc ℓ) where
  Input : ∀ (f : A -> ColistP A) -> (xs : ColistW A) -> SG A f

-- | Syntactic sugar for singleton colist as seed of a SG
Input₁ : ∀ {ℓ} {A : Set ℓ} -> (f : A -> ColistP A) -> A -> SG A f
Input₁ f x = Input f (x ∷ [])

-- | Expresses the semantics of concatMap f over a self generative colist.
-- xs = ys ++ concatMap f xs ≡ ⟦ Input f ys ⟧SG
-- Note that a good behaviour is always defined for such definitions, therefore
-- no proofs about the generative function or the input colist are required.
-- Particularly looping definition are 'closed' producing a finite colist.
-- Otherwise the semantics corresponds exactly to the original definition. 
⟦_⟧SG : ∀ {ℓ} {A : Set ℓ} {f : A -> ColistP A} -> SG A f -> ColistP A
⟦ Input _ [] ⟧SG = []
⟦ Input f (x ∷ xs) ⟧SG = x ∷ ♯ (⟦ Input f (whnf (xs ++ f x))⟧SG)

