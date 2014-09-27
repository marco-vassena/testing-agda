module Test.Input.Generator.Base where

open import Coinduction
open import Data.Nat
open import Data.Empty
open import Data.Unit
open import Data.Sum using (_⊎_)
open import Data.Product using (_×_ ; _,_)
open import Data.Colist using (Colist ; _∷_ ; [])
open import Function
open import Level as L

-- TODO cannot rexpress concat as concatMap id because of mismatching levels ℓ and (suc ℓ) (wrong sort)
-- TODO cannot express it not even as an ad hoc constructor for the same reason
-- is there some workaround?
-- concat : ∀ {ℓ} {A : Set ℓ} -> ColistP (ColistP A) -> ColistP A
-- concat xss = concatMap {!!} {!xss!}

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

NonNull : ∀ {ℓ} {A : Set ℓ} -> Colist A -> Set
NonNull [] = ⊥
NonNull (_ ∷ _) = ⊤

-- Productive data-type
data Prod' {A B : Set} (f : A -> Colist B) : (xs : Colist A) -> Set₁ where
  Base : Prod' f []
  Skip : {x : A} {xs : ∞ (Colist A)} -> Prod' f (♭ xs) -> Prod' f (x ∷ xs)
  Now : {x : A} {xs : ∞ (Colist A)} -> ∞ (Prod' f (♭ xs)) -> NonNull (f x) -> Prod' f (x ∷ xs)

-- Prod is as expressive as IsProductive
-- IsProductive2Prod : ∀ {A B} {f : A -> ColistP B} -> {xs : ColistP A} -> IsProductive f -> Prod f xs
-- IsProductive2Prod {xs = xs} p = {!!}
