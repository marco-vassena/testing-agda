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

-- In this case the ≤′ definition is even more suitable.
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

-- Angelic generator for 
fin-A-gen : GeneratorA ℕ Fin
fin-A-gen zero = []
fin-A-gen (suc n) = F.zero ∷ (♯ (C.map F.suc (fin-A-gen n)))

-- TODO improve, lots of duplicates
fin-D-gen' : ColistP (∃ Fin)
fin-D-gen' = ⟦ (Input₁ f (1 , F.zero)) ⟧SG
  where f : ∃ Fin -> ColistP (∃ Fin)
        f (n , fin) = (, (F.suc fin)) ∷ (♯ (((suc n) , F.zero) ∷ ♯ []))

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

sorted-A-gen : GeneratorA (List ℕ) Sorted
sorted-A-gen [] = nil ∷ (♯ [])
sorted-A-gen (x ∷ []) = (singleton x) ∷ (♯ [])
sorted-A-gen (x ∷ y ∷ xs) with x ≤? y
sorted-A-gen (x ∷ y ∷ xs) | yes p = C.map (cons p) (sorted-A-gen (y ∷ xs))
sorted-A-gen (x ∷ y ∷ xs) | no ¬p = []

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

list-gen : {A : Set} {{ g : SimpleGenerator A }} -> SimpleGenerator (List A)
list-gen {{ g }} = ⟦ list-gen' {{ g }} ⟧P

-- In this case take will retrieve the length ℕ of the vectors which is not really
-- what we wanted
vec-gen' : ∀ {A} -> {{g : SimpleGenerator A}} -> ColistP (∃ (Vec A))
vec-gen' {A} {{g = g}} = ⟦ Input₁ cons-gen (, []) ⟧SG
  where cons-gen : ∃ (Vec A) -> ColistP (∃ (Vec A))
        cons-gen (_ , xs) = map (λ x → , (x ∷ xs)) (fromColist g)

vec-gen : ∀ {A} -> {{g : SimpleGenerator A}} -> GeneratorD ℕ (Vec A)
vec-gen {{g}} = ⟦ vec-gen' {{g}} ⟧P

-- Angelic version
vec-A-gen' : ∀ {A} -> {{g : SimpleGenerator A}} -> (n : ℕ) -> ColistP (Vec A n)
vec-A-gen' zero = [] ∷ (♯ [])
vec-A-gen' {{g = []}} (suc n) = []
vec-A-gen' {A} {{g = x ∷ xs}} (suc n) = concatMap gen { λ _ → _ } (vec-A-gen' {{x ∷ xs}} n)
  where 
        ys : ColistP A
        ys = fromColist (x ∷ xs)

        gen : Vec A n -> ColistP (Vec A (suc n))
        gen v = map (flip _∷_ v) ys
        
vec-A-gen : ∀ {A} -> {{g : SimpleGenerator A}} -> GeneratorA ℕ (Vec A)
vec-A-gen {{g}} = ⟦_⟧P ∘ (vec-A-gen' {{g}})

--------------------------------------------------------------------------------
-- Example of using map and map'

-- Each number successor of Even is Odd
odd-gen : GeneratorD ℕ (¬_ ∘ Even)
odd-gen = C.map (P.map suc next-odd) even-genD
  where next-odd : ∀ {n} -> Even n -> ¬ (Even (suc n))
        next-odd isEven0 ()
        next-odd (isEven+2 p) (isEven+2 x) = next-odd p x


data _∈_ {A : Set} : A -> List A -> Set where 
  here : ∀ x xs -> x ∈ (x ∷ xs)
  there : ∀ x y {ys} -> x ∈ ys -> x ∈ (y ∷ ys) 

-- TODO overly complicated
-- ∈-gen' : ∀ {A} -> {{g : SimpleGenerator A}} -> ColistP (∃ {A = A × List A} (λ x → proj₁ x ∈ proj₂ x))
-- ∈-gen' {{g = []}} = []
-- ∈-gen' {A} {{g = (g₁ ∷ gs)}} = (_ , (here g₁ [])) ∷ ♯ (hs ++ (concatMap (there-gen g₁ (♭ gs)) {isProd} (∈-gen' {{g₁ ∷ gs}})))
--   where hs = zipWith (λ x ys → , here x ys) (fromColist (g₁ ∷ gs)) (fromColist (list-gen {{g₁ ∷ gs}}))

--         there-gen : A -> SimpleGenerator A -> ∃ {A = A × List A} (λ x → proj₁ x ∈ proj₂ x)
--                                            -> ColistP (∃ {A = A × List A} (λ x → proj₁ x ∈ proj₂ x))
--         there-gen a [] p  = (_ , (there a a (here a []))) ∷ ♯ []
--         there-gen a (y ∷ ys) ((x , xs) , p) = (_ , there x y p) ∷ ♯ (there-gen a (♭ ys) ((x , xs) , p)) 

--         isProd : IsProductive (there-gen g₁ (♭ gs))
--         isProd _ with ♭ gs
--         isProd _ | [] = _
--         isProd _ | x ∷ xs = _

-- ∈-gen :  ∀ {A} -> {{g : SimpleGenerator A}} -> Colist (∃ {A = A × List A} (λ x → proj₁ x ∈ proj₂ x))
-- ∈-gen {{ g }} = ⟦ (∈-gen' {{ g }}) ⟧P

open import Relation.Binary.PropositionalEquality

-- I have used ℕ here because they can be compared
∈-gen : (x : ℕ) -> GeneratorA (List ℕ) ( _∈_ x )
∈-gen x = ⟦_⟧P ∘ (∈-gen' x)
  where ∈-gen' : (x : ℕ ) (xs : List ℕ) -> ColistP (x ∈ xs)
        ∈-gen' x [] = []
        ∈-gen' x (y ∷ xs) with x Data.Nat.≟ y
        ∈-gen' x (.x ∷ xs) | yes refl = (here x xs) ∷ (♯ (map (there x x) (∈-gen' x xs)))
        ∈-gen' x (y ∷ xs) | no _ = map (there x y) (∈-gen' x xs)

-- Basically the same. It's not even necessary to use ColistP
∈-gen2 : (xs : List ℕ) -> GeneratorA ℕ (flip _∈_ xs)
∈-gen2 xs = ∈-gen' xs
  where ∈-gen' : (xs : List ℕ) (x : ℕ) -> Colist (x ∈ xs)
        ∈-gen' [] x = []
        ∈-gen' (y ∷ xs) x with x Data.Nat.≟ y
        ∈-gen' (.x ∷ xs) x | yes refl = (here x xs) ∷ ♯ (C.map (there x x) (∈-gen' xs x))
        ∈-gen' (y ∷ xs) x | no ¬p = C.map (there x y) (∈-gen' xs x)


-- TODO move to new example module
--------------------------------------------------------------------------------
-- Generators for λ-terms
--------------------------------------------------------------------------------

-- Unit and function types are supported.
data Type : Set where
 O    : Type
 _=>_ : Type -> Type -> Type

ty-gen' : ColistP Type
ty-gen' = O ∷ ♯ (concatMap funTy {isProd} ty-gen')
  where funTy : Type -> ColistP Type
        funTy O = (O => O) ∷ (♯ [])
        funTy (ty₁ => ty₂) = (ty₁ => (ty₁ => ty₂)) ∷ (♯ (( (ty₁ => ty₂) => ty₂) ∷ (♯ ((ty₁ => ty₂) => (ty₁ => ty₂) ∷ ♯ []))))

        isProd : IsProductive funTy
        isProd O = _
        isProd (ty => ty₁) = _

-- | Simple Generator for Types.
ty-gen : SimpleGenerator Type
ty-gen = ⟦ ty-gen' ⟧P

-- | Equality on types is Decidable.
_≟-ty_ : (t1 : Type) -> (t2 : Type) -> Dec (t1 ≡ t2)
O ≟-ty O = yes refl
O ≟-ty (t2 => t3) = no (λ ())
(t1 => t2) ≟-ty O = no (λ ())
(t1 => t2) ≟-ty (t3 => t4) with t1 ≟-ty t3 | t2 ≟-ty t4
(t1 => t2) ≟-ty (.t1 => .t2) | yes refl | yes refl = yes refl
(t1 => t2) ≟-ty (.t1 => t4) | yes refl | no ¬p = no (lemma2 ¬p)
  where lemma2 : ∀ {t1 t2 t3 t4} -> ¬ (t2 ≡ t4) -> (t1 => t2) ≡ (t3 => t4) -> ⊥
        lemma2 ¬p refl = ¬p refl 
(t1 => t2) ≟-ty (t3 => t4) | no ¬p | _ = no (lemma1 ¬p) 
  where lemma1 : ∀ {t1 t2 t3 t4} -> ¬ (t1 ≡ t3) -> (t1 => t2) ≡ (t3 => t4) -> ⊥
        lemma1 ¬p refl = ¬p refl 

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

-- f x y , ∀ x ∈ xs ∀ y ∈ ys  
combine' : ∀ {A B C : Set} -> (f : A -> B -> C) -> List A -> List B -> List C
combine' {A} {B} {C} f xs ys = L.concatMap (λ x → L.map (f x) ys) xs

-- What can be produced via application or lookup in the given context
data Productable (G : Context) (ty : Type) : Set where
  Lookup : Ref G ty -> Productable G ty
  Apply : ∀ {ty'} -> Productable G (ty' => ty) -> Productable G ty' -> Productable G ty

-- | Produces a term of the given type in the given context 
-- from a Productable proof object.
produce : ∀ {G ty} -> Productable G ty -> Term G ty
produce (Lookup x) = Var x
produce (Apply f x) = App (produce f) (produce x)

-- If a term of some type can be produced in some environment, then it
-- can be produced in an increased environment.
lift : ∀ {ty ty' G} -> Productable G ty -> Productable (ty' ∷ G) ty
lift (Lookup x) = Lookup (Pop x)
lift (Apply f x) = Apply (lift f) (lift x)

-- Compact representation of a function that produces ty given the types contained in ts
_==>_ : List Type -> Type -> Type
ts ==> ty = L.foldr _=>_ ty ts

-- | Determines whether a type ty' can produce another type by 0 or more applications.
-- If that is the case those types are collected and returned in a list inside the Maybe monad.
subgoals : (ty ty' : Type) -> Maybe (List Type)
subgoals ty ty' with ty ≟-ty ty'
subgoals ty .ty | yes refl = just []
subgoals ty O | no ¬p = nothing
subgoals ty (ty' => ty'') | no ¬p = M.map (_∷_ ty') (subgoals ty ty'')

-- | Collects in a List all the terms of the given type in the given context.
ref-genL : (G : Context) -> (ty : Type) -> List (Ref G ty)
ref-genL [] i = []
ref-genL (ty₁ ∷ G) ty₂ with ty₁ ≟-ty ty₂
ref-genL (ty₁ ∷ G) .ty₁ | yes refl = Top ∷ (L.map Pop (ref-genL G ty₁))
ref-genL (ty₁ ∷ G) ty₂ | no ¬p = L.map Pop (ref-genL G ty₂)

-- | Angelic generator for reference data-type
ref-gen : (G : Context) -> GeneratorA Type (Ref G)
ref-gen G ty = C.fromList (ref-genL G ty)

-- | Angelic generator for the Productable data type.
-- It returns a List because of productivity issues.
productable-genL : (G : Context) -> (ty : Type) -> List (Productable G ty)
productable-genL G ty = L.concatMap (λ ts → (apply-gen ts (lookup-gen _))) (L.gfilter (subgoals ty) G)
  where lookup-gen : (ty : Type) -> List (Productable G ty)
        lookup-gen ty = L.map Lookup (ref-genL G ty)

        apply-gen : (ts : List Type) -> List (Productable G (ts ==> ty)) -> List (Productable G ty)
        apply-gen [] ps = ps
        apply-gen (ty₁ ∷ []) ps = combine' Apply ps (lookup-gen ty₁)
        apply-gen (ty₁ ∷ ty₂ ∷ ts) ps = apply-gen (ty₂ ∷ ts) (combine' Apply ps xs₁)
          where xs₁ = lookup-gen ty₁

-- | Angelic generator for the Productable data type.
productable-gen : (G : Context) -> GeneratorA Type (Productable G)
productable-gen G ty = C.fromList (productable-genL G ty)

-- | Angelic generator for the λ-terms of the given type in the given context.
term-gen : (G : Context) -> GeneratorA Type (Term G)
term-gen G O = C.map produce (productable-gen G O)
term-gen G (ty₁ => ty₂) = C.map produce (productable-gen G _) C.++ C.map Abs (term-gen (ty₁ ∷ G) ty₂)
