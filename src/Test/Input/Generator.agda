module Test.Input.Generator where

open import Data.Nat
open import Data.Bool
open import Data.List using (List ; [] ; _∷_ ; [_])
open import Data.Colist using (Colist ; [] ; _∷_)
open import Data.BoundedVec.Inefficient using (BoundedVec ; [] ; _∷_)
import Data.BoundedVec.Inefficient as BVec
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
-- generator' = Stream (∃ (i : I) -> (T i))

-- Not the right interface ... Not many similar proofs that n is even
-- even-gen : Generator Even
-- even-gen zero = isEven0 ∷ (♯ [])
-- even-gen (suc n) = []

-- It does not work because Colist/Stream/Lists are homogeneous
-- even-gen : {!!}
-- even-gen = go isEven0
--   where go : ∀ {n} -> Even n -> Colist {!!}
--         go p = p ∷ (♯ go {!isEven+2 p!}) 

-- TODO I can be implicit
-- TODO p : I -> Set ℓ , otherwise it might be difficult to
-- use _×_ and other constructs

data Generator (I : Set) (p : I -> Set) : Set₁ where
     [] : Generator I p
     _∷_ : ∀ {i : I} (x : p i) -> (xs : ∞ (Generator I p)) -> Generator I p

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
-- | Change the index and the predicate
map' : ∀ {I J} {p q} -> (f : I -> J) (g : {i : I} -> p i -> q (f i)) -> Generator I p -> Generator J q
map' f g [] = []
map' f g (x ∷ xs) = (g x) ∷ ♯ map' f g (♭ xs)

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

-- Promising common pattern
-- Base cases can be generated directly.
-- Recursively cases are recursive calls to the generator

-- This works well when there is a specialized data-type that models
-- the property sought. 

-- Generator of Even numbers
even-gen : Generator ℕ Even
even-gen = go isEven0
  where go : ∀ {n : ℕ} -> Even n -> Generator ℕ Even
        go p = p ∷ (♯ (go (isEven+2 p)))

-- Generates proof objects for all numbers ≤ n
-- This is more difficult because it is a specialization of the generic 
-- binary relation ≤ and particularly the right hand side of ≤ changes in the
-- definitions.
-- Furthermore we are exploiting specific information about the ≤ relation in ℕ.
≤-gen : (n : ℕ) ->  Generator ℕ (flip _≤_ n)
≤-gen n = go 0
  where go : ℕ -> Generator ℕ (flip _≤_ n)
        go m with m ≤? n      -- BAD : This requires ≤ to be decidable and it's not different from the ⇒ construct
        go m | yes p = p ∷ ♯ (go (suc m))
        go m | no ¬p = []

open import Data.Stream using (Stream ; _∷_)

-- Here instead we are following the pattern given by the constructors of ≤.
-- This is easier here because of ≤ definition for the lhs.

≤-gen' : (n : ℕ) ->  Generator ℕ (_≤_ n)
≤-gen' zero = go nats
  where go : Stream ℕ -> Generator ℕ ( _≤_ 0)
        go (x ∷ xs) = _∷_ {i = x} z≤n (♯ (go (♭ xs)))
≤-gen' (suc n) = go (≤-gen' n)
  where go : ∀ {n} -> Generator ℕ (_≤_ n) -> Generator ℕ (_≤_ (suc n))
        go [] = []
        go (x ∷ xs) = (s≤s x) ∷ ♯ (go (♭ xs)) 

-- In this case the ≤′ definition is even more suitable.
≤′-gen : (n : ℕ) -> Generator ℕ (_≤′_ n)
≤′-gen n = go ≤′-refl
  where go : ∀ {m} -> n ≤′ m -> Generator ℕ (_≤′_ n)
        go p = p ∷ ♯ (go (≤′-step p))

≤-refl  : ∀ m -> m ≤ m
≤-refl zero = z≤n
≤-refl (suc m) = s≤s (≤-refl m)

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
        
        gen : ∀ {xs} -> Sorted xs -> Generator (List ℕ) Sorted
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



-- Generator for non dependent types
SimpleGenerator : Set -> Set
SimpleGenerator A = Colist A

-- | Generates boolean values
bool-gen : SimpleGenerator Bool
bool-gen = true ∷ ♯ (false ∷ ♯ [])

-- | Generates all the natural numbers
nat-gen : SimpleGenerator ℕ
nat-gen = go 0
  where go : ℕ -> SimpleGenerator ℕ
        go n = n ∷ ♯ (go (suc n))

list-gen : {A : Set} {{ g : SimpleGenerator A }} -> SimpleGenerator (List A)
list-gen {{g = g}} = [] ∷ ♯ (longer g (list-gen {{g}}))
  where cons-gen : ∀ {A} -> List A -> SimpleGenerator A -> SimpleGenerator (List A)
        cons-gen xs [] = []
        cons-gen xs (y ∷ ys) = (y ∷ xs) ∷ ♯ (cons-gen xs (♭ ys))

        singles : ∀ {A} -> SimpleGenerator A -> SimpleGenerator (List A)
        singles [] = []
        singles (x ∷ xs) = [ x ] ∷ ♯ (singles (♭ xs))

        longer : ∀ {A} -> SimpleGenerator A -> SimpleGenerator (List A) -> SimpleGenerator (List A)
        longer g [] = []
        longer g (x ∷ xs) = (cons-gen x g) C.++ longer g (♭ xs)

open import Data.Vec using (Vec ; _∷_ ; [])
import Data.Vec as V

-- In this case take will retrieve the length ℕ of the vectors which is not really
-- what we wanted
vec-gen : ∀ {A} -> {{g : SimpleGenerator A}} -> Generator ℕ (Vec A)
vec-gen {{g = g}} = [] ∷ ♯ (longer g (vec-gen {{g}}))
  where cons-gen : ∀ {A n} -> Vec A n -> SimpleGenerator A -> Generator ℕ (Vec A)
        cons-gen xs [] = []
        cons-gen xs (y ∷ ys) = (y ∷ xs) ∷ ♯ (cons-gen xs (♭ ys))

        longer : ∀ {A} -> SimpleGenerator A -> Generator ℕ (Vec A) -> Generator ℕ (Vec A)
        longer g [] = []
        longer g (x ∷ xs) = (cons-gen x g) +++ longer g (♭ xs)

-- TODO examples for:
--   rosetree
--   vector

--------------------------------------------------------------------------------
-- Example of using map and map'

-- Each number successor of Even is Odd
odd-gen : Generator ℕ (¬_ ∘ Even)
odd-gen = map' suc next-odd even-gen
  where next-odd : ∀ {n} -> Even n -> ¬ (Even (suc n))
        next-odd isEven0 ()
        next-odd (isEven+2 p) (isEven+2 x) = next-odd p x

open import Data.Product

data _∈_ {A : Set} : A -> List A -> Set where 
  here : ∀ x xs -> x ∈ (x ∷ xs)
  there : ∀ x y {ys} -> x ∈ ys -> x ∈ (y ∷ ys) 

-- TODO can be improved
∈-gen : ∀ {A} -> {{g : SimpleGenerator A}} -> Generator (A × List A) (λ x → proj₁ x ∈ proj₂ x)
∈-gen {A} {{g = g}} = here-gen g (list-gen {{g}}) +++ there-gen g (∈-gen {{g}}) 
  where 
        here-gen : SimpleGenerator A -> SimpleGenerator (List A) -> Generator (A × List A) (λ x → proj₁ x ∈ proj₂ x)
        here-gen (x ∷ xs) (ys ∷ yss) = here x ys ∷ (♯ (here-gen (♭ xs) (ys ∷ yss))) 
        here-gen _ _ = []

        there-gen : SimpleGenerator A -> Generator (A × List A) (λ x → proj₁ x ∈ proj₂ x)
                                      -> Generator (A × List A) (λ x → proj₁ x ∈ proj₂ x)
        there-gen (x ∷ xs) (_∷_ {i = i} y ys) = (there (proj₁ i) x y) ∷ ♯ (there-gen (♭ xs) (y ∷ ys))
        there-gen _ _ = []

-- TODO combinators for dealing with generation of multiple values

-- Example lambda terms

-- Unit and function types are supported.
data Type : Set where
 O    : Type
 _=>_ : Type -> Type -> Type

ty-gen : SimpleGenerator Type
ty-gen = O ∷ ♯ ((O => O) ∷ (♯ (fun ty-gen)))
  where fun : SimpleGenerator Type -> SimpleGenerator Type
        fun [] = []
        fun (x ∷ xs) with ♭ xs
        fun (x ∷ xs) | [] = []
        fun (x ∷ xs) | y ∷ ys = (x => y) ∷ (♯ ((y => x) ∷ (♯ ((y => y) ∷ (♯ (fun (y ∷ ys)))))))

-- Type context: the top of this list is the type of the innermost
-- abstraction variable, the next element is the type of the next
-- variable, and so on.
Context : Set
Context = List Type

-- Reference to a variable, bound during some abstraction.
data Ref : Context -> Type -> Set where
 Top : forall {G u} -> Ref (u ∷ G) u
 Pop : forall {G u v} -> Ref G u -> Ref (v ∷ G) u

-- A term in the lambda calculus. The language solely consists of
-- abstractions, applications and variable references.
data Term : Context -> Type -> Set where
 Abs : forall {G u v} -> Term (u ∷ G) v -> Term G (u => v)
 App : forall {G u v} -> Term G (u => v) -> Term G u -> Term G v
 Var : forall {G u} -> Ref G u -> Term G u

fun-gen : Generator Context (λ G → Term G (O => O))
fun-gen = {!!}

-- Suppose we want to generate terms that have some type α
-- Writing a generator for the data type Term is not the way
-- because the indexes are Context and Type, instead it needs
-- to be a Term

-- data FunType (G : Context) (a b : Type) : Term G (a => b) -> Set where
--   Lambda : (t : Term (a ∷ G) b) -> FunType G a b (Abs t)
