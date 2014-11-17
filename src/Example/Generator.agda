module Example.Generator where

open import Coinduction
open import Data.Nat
open import Data.Bool
open import Data.Colist using (Colist ; [] ; _∷_ )
import Data.Colist as C
open import Data.List using (List ; [] ; _∷_ ; [_])
import Data.List as L
open import Data.Product using (∃ ; _,_ ; _×_ ; proj₁ ; proj₂ ; ,_)
import Data.Product as P
open import Data.Maybe using (just ; nothing ; Maybe)
import Data.Maybe as M
open import Data.Vec using (Vec ; _∷_ ; [])
import Data.Vec as V
open import Data.Empty
open import Relation.Nullary
open import Function

open import Example.Even using (Even ; isEven+2 ; isEven0)
open import Test.Input.Generator
open import Test.Input.Generator.Base

--------------------------------------------------------------------------------
-- Examples of generators for non dependent types
--------------------------------------------------------------------------------

-- | Generates boolean values
bool-gen : SimpleGenerator Bool
bool-gen = true ∷ ♯ (false ∷ ♯ [])

-- | Generates all the natural numbers
nat-gen : SimpleGenerator ℕ
nat-gen = ⟦ iterate suc 0 ⟧P

list-gen' : {A : Set} {{ g : SimpleGenerator A }} -> ColistP (List A)
list-gen' {A} {{g}} = ⟦ Input₁ f [] ⟧SG
  where f : List A -> ColistP (List A)
        f xs = map (flip _∷_ xs) (fromColist g)

-- | Given a generator for A produces a Generator for lists of A.
list-gen : {A : Set} {{ g : SimpleGenerator A }} -> SimpleGenerator (List A)
list-gen {{ g }} = ⟦ list-gen' {{ g }} ⟧P

--------------------------------------------------------------------------------
-- Generators for dependent types
--------------------------------------------------------------------------------

-- Demoniac generator of eveness proofs
even-genD : GeneratorD ℕ Even
even-genD = ⟦ iterate (P.map (suc ∘ suc) isEven+2) (, isEven0) ⟧P

-- Angelic generator of eveness proofs.
-- Negative example: one and only one proof can be produced if 
-- the number is even in the first place
even-genA : GeneratorA ℕ Even
even-genA zero = isEven0 ∷ (♯ [])
even-genA (suc zero) = []
even-genA (suc (suc n)) = C.map isEven+2 (even-genA n)

-- Generates proof objects for all numbers ≤ n
-- This is more difficult because it is a specialization of the generic 
-- binary relation ≤ and particularly the right hand side of ≤ changes in the
-- definitions.
-- Furthermore we are exploiting specific information about the ≤ relation in ℕ.
≤-genD : (n : ℕ) -> GeneratorD ℕ (flip _≤_ n)
≤-genD n = go 0
  where go : ℕ -> GeneratorD ℕ (flip _≤_ n)
        go m with m ≤? n      -- BAD : This requires ≤ to be decidable and it's not different from the ⇒ construct
        go m | yes p = (_ , p) ∷ ♯ (go (suc m))
        go m | no ¬p = []

-- Angelic generator of ≤ proofs.
-- This is another negative example of a bad choice of interface.
≤-genA : (n : ℕ) -> GeneratorA ℕ (flip _≤_ n)
≤-genA n zero = z≤n ∷ (♯ [])
≤-genA zero (suc m) = []
≤-genA (suc n) (suc m) = C.map s≤s (≤-genA n m)

-- Another similar generator for ≤ relation : numbers greater or equal than n 
-- Here instead we are following the pattern given by the constructors of ≤.
-- This is easier here because of ≤ definition for the lhs of ≤.
≤-gen' : (n : ℕ) ->  GeneratorD ℕ (_≤_ n)
≤-gen' zero = ⟦ gen0 ⟧P
  where gen0 : ColistP (∃ (_≤_ zero))
        gen0 = (zero , z≤n) ∷ (♯ (map (λ x → suc (proj₁ x) , z≤n) gen0))
≤-gen' (suc n) = C.map (P.map suc s≤s) (≤-gen' n)

-- In this case the ≤′ definition is more suitable.
≤′-gen : (n : ℕ) -> GeneratorD ℕ (_≤′_ n)
≤′-gen n = ⟦ iterate (P.map suc ≤′-step) (n , ≤′-refl) ⟧P

>-gen : (n : ℕ) ->  GeneratorD ℕ (flip _>_ n)
>-gen n = ⟦ gen ⟧P
  where ≤-refl  : ∀ m -> m ≤ m
        ≤-refl zero = z≤n
        ≤-refl (suc m) = s≤s (≤-refl m)

        lb : ∀ {n m} -> m > n -> (suc m) > n
        lb {m = zero} ()
        lb {n = zero} {m = suc m} p = s≤s z≤n
        lb {n = suc n} {m = suc m} p = s≤s (lb (≤-pred p))
        
        gen : ColistP (∃ (flip _>_ n))
        gen = (suc n , s≤s (≤-refl n)) ∷ ♯ (map (P.map suc lb) gen)

open import Data.Fin using (Fin)
import Data.Fin as F

-- Angelic generator for Fin
fin-A-gen : GeneratorA ℕ Fin
fin-A-gen zero = []
fin-A-gen (suc n) = F.zero ∷ (♯ (C.map F.suc (fin-A-gen n)))

fin-D-gen' : ColistP (∃ Fin)
fin-D-gen' = ⟦ (Input₁ f (1 , F.zero)) ⟧SG
  where f : ∃ Fin -> ColistP (∃ Fin)
        f (n , fin) = (, (F.suc fin)) ∷ (♯ (((suc n) , F.zero) ∷ ♯ []))

-- Demoniac generator for Fin
fin-D-gen : GeneratorD ℕ Fin
fin-D-gen = ⟦ fin-D-gen' ⟧P

-- Proof objected that the indexed list is sorted.
data Sorted : List ℕ -> Set where
  nil : Sorted []
  singleton : ∀ n -> Sorted (n ∷ []) 
  cons : ∀ {x y xs} → x ≤ y → Sorted (y ∷ xs) → Sorted (x ∷ y ∷ xs)

sorted-gen' : ℕ -> ColistP (∃ Sorted)
sorted-gen' n = ⟦ Input cons-gen ((, nil) ∷ singles n) ⟧SG
  where singles : ℕ -> ColistP (∃ Sorted)
        singles zero = (_ , (singleton zero)) ∷ (♯ [])
        singles (suc n) = (_ , (singleton (suc n))) ∷ ♯ (singles n)
        
        cons-gen : ∃ Sorted -> ColistP (∃ Sorted)
        cons-gen ([] , nil) = []
        cons-gen (.m ∷ [] , singleton m) = map (λ x → , (cons (proj₂ x) (singleton m))) (fromColist (≤-genD m))
        cons-gen ( ._ , cons {n} leq p) = map (λ x → , (cons (proj₂ x) (cons leq p))) (fromColist (≤-genD n))

-- | Produces all the sorted lists of arbitrary length using numbers up to n, without duplicates
sorted-gen : ℕ -> GeneratorD (List ℕ) Sorted
sorted-gen n = ⟦ (sorted-gen' n) ⟧P

-- Angelic generator for proofs of sortedness.
-- Negative example: one and only one proof exists
-- if the given list is sorted in the first place.
sorted-A-gen : GeneratorA (List ℕ) Sorted
sorted-A-gen [] = nil ∷ (♯ [])
sorted-A-gen (x ∷ []) = (singleton x) ∷ (♯ [])
sorted-A-gen (x ∷ y ∷ xs) with x ≤? y
sorted-A-gen (x ∷ y ∷ xs) | yes p = C.map (cons p) (sorted-A-gen (y ∷ xs))
sorted-A-gen (x ∷ y ∷ xs) | no ¬p = []

-- In this case take will retrieve the length ℕ of the vectors which is not really
-- what we wanted
vec-gen' : ∀ {A} -> {{g : SimpleGenerator A}} -> ColistP (∃ (Vec A))
vec-gen' {A} {{g = g}} = ⟦ Input₁ cons-gen (, []) ⟧SG
  where cons-gen : ∃ (Vec A) -> ColistP (∃ (Vec A))
        cons-gen (_ , xs) = map (λ x → , (x ∷ xs)) (fromColist g)

-- | Demoniac generator for vectors
-- Negative examples : what can be actually retrieved is the index, i.e.
-- the length of the vector, which is instead discarded.
vec-gen : ∀ {A} -> {{g : SimpleGenerator A}} -> GeneratorD ℕ (Vec A)
vec-gen {{g}} = ⟦ vec-gen' {{g}} ⟧P

vec-A-gen' : ∀ {A} -> {{g : SimpleGenerator A}} -> (n : ℕ) -> ColistP (Vec A n)
vec-A-gen' zero = [] ∷ (♯ [])
vec-A-gen' {{g = []}} (suc n) = []
vec-A-gen' {A} {{g = x ∷ xs}} (suc n) = concatMap gen { λ _ → _ } (vec-A-gen' {{x ∷ xs}} n)
  where 
        ys : ColistP A
        ys = fromColist (x ∷ xs)

        gen : Vec A n -> ColistP (Vec A (suc n))
        gen v = map (flip _∷_ v) ys

-- Angelic version for vectors
-- Positive example : Given the index (the length of the vector) we can produce
-- efficiently vectors of that length.
vec-A-gen : ∀ {A} -> {{g : SimpleGenerator A}} -> GeneratorA ℕ (Vec A)
vec-A-gen {{g}} = ⟦_⟧P ∘ (vec-A-gen' {{g}})

--------------------------------------------------------------------------------

-- Manipulating the eveness generator we can produce a generator for odd numbers. 
odd-genD : GeneratorD ℕ (¬_ ∘ Even)
odd-genD = C.map (P.map suc next-odd) even-genD
  where next-odd : ∀ {n} -> Even n -> ¬ (Even (suc n))
        next-odd isEven0 ()
        next-odd (isEven+2 p) (isEven+2 x) = next-odd p x


data _∈_ {A : Set} : A -> List A -> Set where 
  here : ∀ x xs -> x ∈ (x ∷ xs)
  there : ∀ x y {ys} -> x ∈ ys -> x ∈ (y ∷ ys) 

-- TODO overly complicated
∈-genD' :  ∀ {A} -> {{g : SimpleGenerator A}} -> ColistP (∃ {A = A × List A} (λ x → proj₁ x ∈ proj₂ x))
∈-genD' {{g = []}} = []
∈-genD' {A} {{g = x ∷ xs}} = ⟦ (Input₁ (there-gen x (x ∷ xs)) (, (here x []))) ⟧SG
  where there-gen :  A -> SimpleGenerator A -> ∃ {A = A × List A} (λ x → proj₁ x ∈ proj₂ x)
                                            -> ColistP (∃ {A = A × List A} (λ x → proj₁ x ∈ proj₂ x))
        there-gen a [] ((y , ys) , p) = (, there a a (here a [])) ∷ ♯ []
        there-gen a (y ∷ ys) ((x , xs) , p) = (, there x y p) ∷ ♯ there-gen a (♭ ys) ((x , xs) , p)

∈-genD :  ∀ {A} -> {{g : SimpleGenerator A}} -> Colist (∃ {A = A × List A} (λ x → proj₁ x ∈ proj₂ x))
∈-genD {{ g }} = ⟦ (∈-genD' {{ g }}) ⟧P

open import Relation.Binary.PropositionalEquality

-- Angelic Generator for ∈ proofs.
-- Negative example : it basically checks whether the
-- given values is present in the list or not.
∈-genA : (x : ℕ) -> GeneratorA (List ℕ) ( _∈_ x )
∈-genA x = ⟦_⟧P ∘ (∈-genA' x)
  where ∈-genA' : (x : ℕ ) (xs : List ℕ) -> ColistP (x ∈ xs)
        ∈-genA' x [] = []
        ∈-genA' x (y ∷ xs) with x Data.Nat.≟ y
        ∈-genA' x (.x ∷ xs) | yes refl = (here x xs) ∷ (♯ (map (there x x) (∈-genA' x xs)))
        ∈-genA' x (y ∷ xs) | no _ = map (there x y) (∈-genA' x xs)

