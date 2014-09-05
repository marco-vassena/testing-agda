module Test.Input.Generator where

open import Data.Nat
open import Data.Conat
open import Data.Bool
open import Data.List using (List ; [] ; _∷_)
open import Data.Colist using (Colist ; [] ; _∷_)
open import Data.BoundedVec.Inefficient as BVec
import Data.Colist as C
open import Function
open import Coinduction
open import Relation.Nullary
open import Example.Even

--------------------------------------------------------------------------------
-- Data type for generator
--------------------------------------------------------------------------------
-- TODO move to new module

-- Stream vs Colist
-- I would choose for CoList
--   some enumeration are inherently finite
--   some are empty
-- But still we might want to model those

-- Angelic version
-- This is not exactly what we want, see Even example
-- Generator : ∀ {I : Set} -> (I -> Set) -> Set
-- Generator {I} T = ∀ (i : I) -> Colist (T i)


-- Demoniac version - Not sure how to translate this
-- generator' : ∀ {I} -> Set
-- generator' = Stream (∃ (T i))

-- Not the right interface ... Not many similar proofs that n is even
-- even-gen : Generator Even
-- even-gen zero = isEven0 ∷ (♯ [])
-- even-gen (suc n) = []

-- It does not work because Colist/Stream/Lists are homogeneous
-- even-gen : {!!}
-- even-gen = go isEven0
--   where go : ∀ {n} -> Even n -> Colist {!!}
--         go p = p ∷ (♯ go {!isEven+2 p!}) 

data Generator (I : Set) : (p : I -> Set) -> Set₁ where
     [] : ∀ {p} -> Generator I p
     _∷_ : ∀ {i : I} {p} -> (x : p i) -> (xs : ∞ (Generator I p)) -> Generator I p

_+++_ : ∀ {I p} -> Generator I p -> Generator I p -> Generator I p
[] +++ ys = ys
(x ∷ xs) +++ ys = x ∷ ♯ (♭ xs +++ ys)

_+++'_ : ∀ {I p} -> Generator I p -> ∞ (Generator I p) -> Generator I p
[] +++' ys = ♭ ys
(x ∷ xs) +++' ys = x ∷ ♯ (♭ xs +++' ys)
 
-- | Change the predicate, keep the same index
map : ∀ {I} {p q} -> (∀ {i : I} -> p i -> q i) -> Generator I p -> Generator I q
map f [] = []
map f (x ∷ xs) = f x ∷ (♯ (map f (♭ xs)))

-- TODO can be fused in only one map ?
-- | Change also index
map' : ∀ {I J} {p q} {j : J} -> (∀ {i : I} -> p i -> q j) -> Generator I p -> Generator J q
map' f [] = []
map' f (x ∷ xs) = (f x) ∷ (♯ map' f (♭ xs))

concatMap : ∀ {I p q} -> (∀ {i : I} -> p i -> Generator I q) -> Generator I p -> Generator I q
concatMap f [] = []
concatMap f (x ∷ xs) = (f x) +++ (concatMap f (♭ xs)) -- Why is this red?

concatMap' : ∀ {I p q} -> (∀ {i : I} -> p i -> Generator I q) -> Generator I p -> Generator I q
concatMap' f [] = []
concatMap' f (x ∷ xs) = (f x) +++' ♯ (concatMap' f (♭ xs)) -- Also this fails (even though the recursive call is guarded)


-- | Collects the input values (in which we are ultimately interested) from a Colist
-- of proof objects
toColist : ∀ {I : Set} {p : I -> Set} -> Generator I p -> Colist I
toColist [] = []
toColist (_∷_ {i = i} x xs) = i ∷ ♯ (toColist (♭ xs))

take : ∀ {I : Set} {p : I -> Set} -> (n : ℕ) -> Generator I p -> BoundedVec I n
take n = C.take n ∘ toColist 

-- TODO remove?
-- | This is actually not really useful because of the signature of f.
-- It's rare that for any I the property p holds.
-- Choosing I such that f is trivial is not an option
generate : {I : Set} -> {p : I -> Set} -> (f : ∀ (i : I) -> p i) -> Colist I -> Generator I p
generate f [] = []
generate f (x ∷ xs) = f x ∷ ♯ (generate f (♭ xs))

--------------------------------------------------------------------------------
-- Examples
--------------------------------------------------------------------------------
-- TODO move to Example module

-- Generator of Even numbers
even-gen : Generator ℕ Even
even-gen = go isEven0
  where go : ∀ {n : ℕ} -> Even n -> Generator ℕ Even
        go p = p ∷ (♯ (go (isEven+2 p)))

-- Generates proof objects for all numbers ≤ n
≤-gen : (n : ℕ) ->  Generator ℕ (flip _≤_ n)
≤-gen n = go 0
  where go : ℕ -> Generator ℕ (flip _≤_ n )
        go m with m ≤? n      -- This requires ≤ to be decidable
        go m | yes p = p ∷ ♯ (go (suc m))
        go m | no ¬p = []

≤-refl  : ∀ m -> m ≤ m
≤-refl zero = z≤n
≤-refl (suc m) = s≤s (≤-refl m)

≤-gen1 : (n : ℕ) -> Generator ℕ (flip _≤_ n)

≤-gen1 n with n | ≤-refl n
≤-gen1 n | zero | z≤n = z≤n ∷ (♯ [])
≤-gen1 n | suc m | s≤s r = s≤s r ∷ {!♯ ≤-gen1 m!}
  where cong : (Generator ℕ (flip _≤_ m)) -> (Generator ℕ (flip _≤_ (suc m)))
        cong [] = []
        cong (x ∷ xs) = {!!}
  -- where go : (m : ℕ) -> m Data.Nat.≤ n -> Generator ℕ (flip _≤_ n)
  --       go zero z≤n = z≤n ∷ (♯ [])
  --       go (suc m) p with n
  --       go (suc m) () | zero
  --       go (suc m) (s≤s p) | suc n = (s≤s p) ∷ (♯ {!go ? ?!}) -- p ∷ (♯ (go m (≤-pred {!p!})))


>-gen : (n : ℕ) ->  Generator ℕ (flip _>_ n)
>-gen n = go (suc n) (s≤s (≤-refl n))
  where 
        lb : ∀ {n m} -> m > n -> (suc m) > n
        lb {m = zero} ()
        lb {n = zero} {m = suc m} p = s≤s z≤n
        lb {n = suc n} {m = suc m} p = s≤s (lb (≤-pred p))

        go : (m : ℕ) -> (m > n) -> Generator ℕ (flip _>_ n) 
        go m p = p ∷ ♯ (go (suc m) (lb p))

-- I will consider only ℕ to make things easier for the time being
data Sorted : List ℕ -> Set where
  nil : Sorted []
  singleton : ∀ n -> Sorted (n ∷ []) 
  cons : ∀ {x y xs} → x ≤ y → Sorted (y ∷ xs) → Sorted (x ∷ y ∷ xs)

-- | Produces all the sorted lists of arbitrary length using numbers up to n, without duplicates
sorted-gen : ℕ -> Generator (List ℕ) Sorted
sorted-gen n = nil ∷ ♯ (singles n +++ longer (sorted-gen n))
  where singles : ℕ -> Generator (List ℕ) Sorted
        singles zero = (singleton zero) ∷ ♯ []
        singles (suc n) = singleton (suc n) ∷ ♯ (singles n)
        
        gen : ∀ {xs} -> Sorted xs -> Generator (List ℕ)  Sorted
        gen nil = []
        gen (singleton m) = go (≤-gen m)
          where go : Generator ℕ (flip _≤_ m) -> Generator (List ℕ) Sorted
                go [] = []
                go (x ∷ xs) = (cons x (singleton m)) ∷ ♯ (go (♭ xs))
        gen (cons {n} x p) = go (≤-gen n)
          where go : Generator ℕ (flip _≤_ n) -> Generator (List ℕ) Sorted 
                go [] = []
                go (y ∷ ys) = (cons y (cons x p)) ∷ ♯ (go (♭ ys))

        longer : Generator (List ℕ) Sorted -> Generator (List ℕ) Sorted
        longer xs = concatMap gen xs         

open import Data.Unit

-- Generator for non dependent types
SimpleGenerator : Set -> Set₁
SimpleGenerator A = Generator ⊤ (const A)

-- | Generates boolean values
bool-gen : SimpleGenerator Bool
bool-gen = true ∷ ♯ (false ∷ ♯ [])

-- | Generates all the natural numbers
nat-gen : SimpleGenerator ℕ
nat-gen = go 0
  where go : ℕ -> SimpleGenerator ℕ
        go n = n ∷ ♯ (go (suc n))

list-gen : {A : Set} {{ g : SimpleGenerator A }} -> SimpleGenerator (List A)
list-gen {{ g = g }} = {!!}

-- TODO examples for:
--   rosetree
--   vector
