module Example.Generator where

open import Coinduction
open import Data.Nat
open import Data.Bool
open import Data.Colist using (Colist ; [] ; _∷_ )
import Data.Colist as C
open import Data.List using (List ; [] ; _∷_ ; [_])
open import Data.Product using (∃ ; _,_ ; _×_ ; proj₁ ; proj₂ ; ,_)
import Data.Product as P
open import Relation.Nullary
open import Function

open import Example.Even
open import Test.Input.Generator
open import Test.Input.Generator.Base


-- Generator of Even numbers
even-gen : GeneratorD ℕ Even
even-gen = go isEven0
  where go : ∀ {n : ℕ} -> Even n -> GeneratorD ℕ Even
        go p = (_ , p) ∷ (♯ (go (isEven+2 p)))

-- Generates proof objects for all numbers ≤ n
-- This is more difficult because it is a specialization of the generic 
-- binary relation ≤ and particularly the right hand side of ≤ changes in the
-- definitions.
-- Furthermore we are exploiting specific information about the ≤ relation in ℕ.
≤-gen : (n : ℕ) -> GeneratorD ℕ (flip _≤_ n)


≤-gen n = go 0
  where go : ℕ -> GeneratorD ℕ (flip _≤_ n)
        go m with m ≤? n      -- BAD : This requires ≤ to be decidable and it's not different from the ⇒ construct
        go m | yes p = (_ , p) ∷ ♯ (go (suc m))
        go m | no ¬p = []

-- Angelic version: basically a decision procedure
≤-A-gen : (n : ℕ) -> GeneratorA ℕ (flip _≤_ n)
≤-A-gen n zero = z≤n ∷ (♯ [])
≤-A-gen zero (suc m) = []
≤-A-gen (suc n) (suc m) = C.map s≤s (≤-A-gen n m)


-- Here instead we are following the pattern given by the constructors of ≤.
-- This is easier here because of ≤ definition for the lhs.

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

fin-A-gen : GeneratorA ℕ Fin
fin-A-gen zero = []
fin-A-gen (suc n) = F.zero ∷ (♯ (C.map F.suc (fin-A-gen n)))

fin-D-gen : GeneratorD ℕ Fin
fin-D-gen = {!concatMap!}

-- I will consider only ℕ to make things easier for the time being
data Sorted : List ℕ -> Set where
  nil : Sorted []
  singleton : ∀ n -> Sorted (n ∷ []) 
  cons : ∀ {x y xs} → x ≤ y → Sorted (y ∷ xs) → Sorted (x ∷ y ∷ xs)

sorted-gen' : ℕ -> ColistP (∃ Sorted)
sorted-gen' n = (_ , nil) ∷ ♯ (singles n ++ concatMap gen {isProd} (sorted-gen' n))

  where singles : ℕ -> ColistP (∃ Sorted)
        singles zero = (_ , (singleton zero)) ∷ (♯ [])
        singles (suc n) = (_ , (singleton (suc n))) ∷ ♯ (singles n)
        
        gen : ∃ Sorted -> ColistP (∃ Sorted)
--        gen ([] , nil) = [] -- This makes gen potentially non productive
        gen ([] , nil) = ([] , nil) ∷ (♯ []) -- This introduces duplicates, but it's productive
        gen (.m ∷ [] , singleton m) = go (≤-gen m)
          where go : GeneratorD ℕ (flip _≤_ m) -> ColistP (∃ Sorted)
                go [] = []
                go ((x , p) ∷ xs) = (_ , (cons p (singleton m))) ∷ ♯ (go (♭ xs))
        gen ( ._ , cons {n} x p) = go (≤-gen n)
          where go : GeneratorD ℕ (flip _≤_ n) -> ColistP (∃ Sorted)
                go [] = []
                go ((_ , y) ∷ ys) = (_ , (cons y (cons x p))) ∷ ♯ (go (♭ ys))

        isProd : IsProductive gen
        isProd (.[] , nil) with gen ([] , nil)
        ... | _ = _
        isProd (.(n₁ ∷ []) , singleton n₁) with (gen (n₁ ∷ [] , singleton n₁))
        ... | _ = _
        isProd (._ , cons x₁ p) with gen (_ , cons x₁ p)
        ... | _ = _
        
-- | Produces all the sorted lists of arbitrary length using numbers up to n, without duplicates
sorted-gen : ℕ -> GeneratorD (List ℕ) Sorted
sorted-gen n = ⟦ (sorted-gen' n) ⟧P

-- | Generates boolean values
bool-gen : SimpleGenerator Bool
bool-gen = true ∷ ♯ (false ∷ ♯ [])

-- | Generates all the natural numbers
nat-gen : SimpleGenerator ℕ
nat-gen = ⟦ nat-gen' ⟧P
  where nat-gen' : ColistP ℕ
        nat-gen' = 0 ∷ ♯ (map suc nat-gen')

list-gen' : {A : Set} {{ g : SimpleGenerator A }} -> ColistP (List A)
list-gen' {A} {{g = g}} = [] ∷ ♯ (concatMap (cons-gen g) {isProd} (list-gen' {{g}}))
  where cons-gen : SimpleGenerator A -> List A -> ColistP (List A)
--        cons-gen [] (_ , xs) = [] -- This makes cons-gen possibly non-productive
        cons-gen [] xs = [] ∷ ♯ [] -- Productive but introduces duplicates
        cons-gen (y ∷ ys) xs =  (y ∷ xs) ∷ (♯ (cons-gen (♭ ys) xs))

        isProd : IsProductive (cons-gen g)
        isProd xs with g
        isProd xs | [] = _
        isProd xs | x ∷ _ = _

list-gen : {A : Set} {{ g : SimpleGenerator A }} -> SimpleGenerator (List A)
list-gen {{ g }} = ⟦ list-gen' {{ g }} ⟧P

open import Data.Vec using (Vec ; _∷_ ; [])
import Data.Vec as V

-- In this case take will retrieve the length ℕ of the vectors which is not really
-- what we wanted
vec-gen' : ∀ {A} -> {{g : SimpleGenerator A}} -> ColistP (∃ (Vec A))
vec-gen' {A} {{g = g}} = (_ , []) ∷ ♯ (concatMap (cons-gen g) {isProd} (vec-gen' {{g}}))
  where cons-gen : SimpleGenerator A -> ∃ (Vec A) -> ColistP (∃ (Vec A))
--        cons-gen [] (_ , xs) = [] -- This makes cons-gen possibly non-productive
        cons-gen [] (_ , xs) = (_ , []) ∷ ♯ [] -- Productive but introduces duplicates
        cons-gen (y ∷ ys) (_ , xs) = (_ , (y ∷ xs)) ∷ (♯ (cons-gen (♭ ys) (_ , xs)))

        isProd : IsProductive (cons-gen g)
        isProd (n , xs) with g
        isProd (n , xs) | [] = _
        isProd (n , xs₁) | x ∷ xs = _

-- Alternative definition.
vec-gen'' : ∀ {A} -> {{g : SimpleGenerator A}} -> ColistP (∃ (Vec A))
vec-gen'' {{g = []}} = (_ , []) ∷ (♯ [])
vec-gen'' {A} {{g = g₁ ∷ gs}} = (_ , []) ∷ ♯ (concatMap (cons-gen g₁ (♭ gs)) {isProd} (vec-gen' {{g₁ ∷ gs}}))
  where cons-gen : A -> SimpleGenerator A -> ∃ (Vec A) -> ColistP (∃ (Vec A))
        cons-gen a [] (_ , xs) = (_ , V.[ a ]) ∷ ♯ []
        cons-gen a (y ∷ ys) (_ , xs) = (_ , (y ∷ xs)) ∷ (♯ (cons-gen a (♭ ys) (_ , xs)))

        isProd : IsProductive (cons-gen g₁ (♭ gs))
        isProd (n , xs) with ♭ gs
        isProd (n , xs) | [] = _
        isProd (n , xs₁) | x ∷ xs = _

vec-gen : ∀ {A} -> {{g : SimpleGenerator A}} -> GeneratorD ℕ (Vec A)
vec-gen {{g}} = ⟦ vec-gen'' {{g}} ⟧P

-- Angelic version
vec-A-gen' : ∀ {A} -> {{g : SimpleGenerator A}} -> (n : ℕ) -> ColistP (Vec A n)
vec-A-gen' zero = [] ∷ (♯ [])
vec-A-gen' {{g = []}} (suc n) = []
vec-A-gen' {A} {{g = x ∷ xs}} (suc n) = concatMap (gen (fromColist (x ∷ xs))) { λ _ → _ } (vec-A-gen' {{x ∷ xs}} n)
  where 
        gen : (xs : ColistP A) -> Vec A n -> ColistP (Vec A (suc n))
        gen xs v = map (flip _∷_ v) xs
        
vec-A-gen : ∀ {A} -> {{g : SimpleGenerator A}} -> GeneratorA ℕ (Vec A)
vec-A-gen {{g}} = ⟦_⟧P ∘ (vec-A-gen' {{g}})

-- TODO examples for:
--   rosetree

--------------------------------------------------------------------------------
-- Example of using map and map'

-- Each number successor of Even is Odd
odd-gen : GeneratorD ℕ (¬_ ∘ Even)
odd-gen = C.map (P.map suc next-odd) even-gen
  where next-odd : ∀ {n} -> Even n -> ¬ (Even (suc n))
        next-odd isEven0 ()
        next-odd (isEven+2 p) (isEven+2 x) = next-odd p x

open import Data.Product using (_×_ ; proj₁ ; proj₂)

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

-- Example lambda terms

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

ty-gen : SimpleGenerator Type
ty-gen = ⟦ ty-gen' ⟧P

open import Data.Empty

-- TODO can be written more succintly?

lemma1 : ∀ {t1 t2 t3 t4} -> ¬ (t1 ≡ t3) -> (t1 => t2) ≡ (t3 => t4) -> ⊥
lemma1 ¬p refl = ¬p refl 

lemma2 : ∀ {t1 t2 t3 t4} -> ¬ (t2 ≡ t4) -> (t1 => t2) ≡ (t3 => t4) -> ⊥
lemma2 ¬p refl = ¬p refl 

_≟-ty_ : (t1 : Type) -> (t2 : Type) -> Dec (t1 ≡ t2)
O ≟-ty O = yes refl
O ≟-ty (t2 => t3) = no (λ ())
(t1 => t2) ≟-ty O = no (λ ())
(t1 => t2) ≟-ty (t3 => t4) with t1 ≟-ty t3 | t2 ≟-ty t4
(t1 => t2) ≟-ty (.t1 => .t2) | yes refl | yes refl = yes refl
(t1 => t2) ≟-ty (.t1 => t4) | yes refl | no ¬p = no (lemma2 ¬p)
(t1 => t2) ≟-ty (t3 => t4) | no ¬p | _ = no (lemma1 ¬p) 

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

o-term : Term (O ∷ []) O
o-term = Var Top

o-term' : Term (O ∷ []) O
o-term' = App idTerm (Var Top)
  where idTerm : ∀ {G} -> Term G (O => O)
        idTerm = Abs (Var Top)

-- SKI combinators
S : ∀ {G c b a} ->
    let xTy = c => (b => a)
        yTy = c => b 
        zTy = c in Term G (xTy => (yTy => (zTy => a)))
S = Abs (Abs (Abs (App (App x z) (App y z))))
  where x = Var (Pop (Pop Top))
        y = Var (Pop Top) 
        z = Var Top

I : ∀ {G ty} -> Term G (ty => ty)
I = Abs (Var Top)

K : ∀ {G a b} -> Term G (a => (b => a))
K = Abs (Abs (Var (Pop Top)))

ref-gen : (G : Context) -> GeneratorA Type (Ref G)
ref-gen [] i = []
ref-gen (ty₁ ∷ G) ty₂ with ty₁ ≟-ty ty₂
ref-gen (ty₁ ∷ G) .ty₁ | yes refl = Top ∷ ♯ (C.map Pop (ref-gen G ty₁))
ref-gen (ty₁ ∷ G) ty₂ | no ¬p = C.map Pop (ref-gen G ty₂)

zipWith' : ∀ {A B C : Set} -> (A -> B -> C) -> Colist A -> Colist B -> Colist C
zipWith' f (x ∷ xs) (y ∷ ys) = (f x y) ∷ (♯ (zipWith' f (♭ xs) (♭ ys))) 
zipWith' f _ _ = []

t1 : Term [] ((O => O) => O)
t1 = App {!!} (Abs (Var Top))

t2 : Term [] (O => (O => O))
t2 = Abs (Abs (Var Top)) -- Also: Abs (Abs (Var (Pop Top)))


-- Non terminating, bounded recursion needed.
term-gen' : (G : Context) -> (ty : Type) -> ColistP (Term G ty)
term-gen' G O = map Var (fromColist (ref-gen G O))
term-gen' G (ty₁ => ty₂) = var-gen ++ (abs-gen ++ app-gen)
  where var-gen : ColistP (Term G (ty₁ => ty₂))
        var-gen = map Var (fromColist (ref-gen G (ty₁ => ty₂)))

        abs-gen : ColistP (Term G (ty₁ => ty₂))
        abs-gen = map Abs (term-gen' (ty₁ ∷ G) ty₂)

        f : Type -> ColistP (Term G (ty₁ => ty₂))
        f ty = zipWith App (term-gen' G (ty => (ty₁ => ty₂))) (term-gen' G ty)

        -- app gen is problematic
        app-gen : ColistP (Term G (ty₁ => ty₂))
        app-gen = concatMap f {{!!}} ty-gen'

term-gen : (G : Context) -> GeneratorA Type (Term G)
term-gen G = ⟦_⟧P ∘ (term-gen' G)
