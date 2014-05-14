module Base where

open import Coinduction
open import Data.Bool
open import Data.Nat
open import Data.Stream hiding (take)
open import Data.List hiding (take)
open import Data.Vec hiding (take)
open import Data.Product as P hiding ( ∃ )
open import Reflection
open import Relation.Nullary
open import Function

take : ∀ {a} -> ℕ -> Stream a -> List a
take {a} n = toList ∘ (Data.Stream.take {a} n)

-- Dependent types predicate decidability
Dec' : {Input : Set} -> (P : Input -> Set) -> Set
Dec' {Input} P = (x : Input) -> Dec (P x)

--------------------------------------------------------------------------------
-- ∀-Properties
--------------------------------------------------------------------------------
 
-- Possible results

data Pass : Set where
  Ok : Pass

-- Property falsifiable for an input
data ¬_for_ {Input : Set} (Property : Set) : Input -> Set where
  CounterExample : (x : Input) -> ¬ Property for x 

record ∀Property {Hyp : Set} {Input : Set} : Set₁ where
  constructor Lemma
  field 
    {P} : Input -> Set
    {f} : Hyp -> Input
    dec : Dec' P
    lemma : (h : Hyp) -> P (f h)

forAll : {Hyp : Set} {Input : Set} -> List Hyp -> ∀Property {Hyp} {Input} -> Set
forAll [] _ = Pass
forAll (x ∷ xs) t with (∀Property.dec t) ((∀Property.f t) x)
forAll (x ∷ xs) t | yes p = forAll xs t
forAll (x ∷ xs) t | no ¬p = ¬ (∀Property.P t (∀Property.f t x)) for x

--------------------------------------------------------------------------------
-- ∃Property
--------------------------------------------------------------------------------

-- Results
data NotFound : Set where

data _by_ {Input : Set} (Property : Set) : Input -> Set where
  Exists : (x : Input) -> Property by x

record ∃Property {Hyp : Set} {Input : Set} : Set₁ where
  constructor Lemma
  field 
    {P} : Input -> Set
    {f} : Hyp -> Input
    dec : Dec' P
    lemma : P.∃ (λ h -> P (f h))

-- For existentially qunatified theorems (e.g. ∃ x . P x)
∃ : {Hyp : Set} {Input : Set} -> List Hyp -> ∃Property {Hyp} {Input} -> Set
∃ [] t = NotFound
∃ (x ∷ xs) t with (∃Property.dec t) ((∃Property.f t) x)
∃ (x ∷ xs) t | yes p = (∃Property.P t (∃Property.f t x)) by x
∃ (x ∷ xs) t | no ¬p = ∃ xs t


--------------------------------------------------------------------------------


open import Data.Unit 


mutual 
  -- Universe
  data U : (List Set) -> Set₁ where
    Forall : {A : Set} -> ∀ {xs} -> (p : A -> U xs) -> U (A ∷ xs)
    Exists : {A : Set} -> ∀ {xs} -> (p : A -> U xs) -> U (A ∷ xs)
    Property : (P : Set) -> U []

⟦_⟧ : ∀ {xs} -> U xs -> Set
⟦_⟧ (Forall {A = A} f) = (a : A) → ⟦ f a ⟧
⟦ Exists {A = A} f ⟧ = (a : A) → ⟦ f a ⟧
⟦ Property P ⟧ = Dec P

-- Contains input values for testing a property
data Input : ∀ xs -> U xs -> Set₁ where
  Nil : ∀ {u} -> Input [] u 
  ConsF : ∀ {xs} {A : Set} {u : U xs} -> List A -> Input xs u -> Input (A ∷ xs) (Forall (λ x → u)) 
  ConsE : ∀ {xs} {A : Set} {u : U xs} -> List A -> Input xs u -> Input (A ∷ xs) (Exists (λ x → u)) 

-- Input 
<_> : ∀ {xs} -> U xs -> Set₁
<_> {A ∷ xs} (Forall p) = Input (A ∷ xs) (Forall p)
<_> {A ∷ xs} (Exists p) = Input (A ∷ xs) (Exists p) 
< Property P > = Input [] (Property P)

<_>-iso : ∀ {xs} {u : U xs} -> Input xs u -> < u >
<_>-iso {[]} {Property P} Nil = Nil
<_>-iso {A ∷ xs} {Forall ._} (ConsF x input) = ConsF x input
<_>-iso {A ∷ xs} {Exists ._} (ConsE x input)= ConsE x input

data Testable : Set₁ where
  C : ∀ {A} -> (u : U A) -> (k : ⟦ u ⟧) -> < u > -> Testable

open import Relation.Binary.PropositionalEquality

ex' : U (ℕ ∷ []) 
ex' = Forall {ℕ} (λ n -> Property (n ≡ n))

dec-ex' : ⟦ ex' ⟧
dec-ex' = λ x -> Data.Nat._≟_ x x

ex : U (ℕ ∷ List ℕ ∷ [])
ex =  (Forall {ℕ} (λ n -> Exists {List ℕ} ( λ xs -> Property (n ≡ (length xs)))))

dec-ex : ⟦ ex ⟧
dec-ex = λ n xs → Data.Nat._≟_ n (length xs)

data Result : Set where
  Yes : Result
  No : Result

-- I guess it does not see termination because it stops because ConsF / ConsE are the same constructor.
-- However xs is strictly smaller than x ∷ xs, therefore it terminates. 
test' : ∀ {xs} (u : U xs) -> ⟦ u ⟧ -> < u > -> Result
test' (Forall ._) check (ConsF [] gen) = Yes
test' (Forall ._) check (ConsF {u = u} (x ∷ xs) gen) with test' u (check x) < gen >-iso
test' (Forall ._) check (ConsF (x ∷ xs) gen) | Yes = test' (Forall _) check (ConsF xs gen)
test' (Forall ._) check (ConsF (x ∷ xs) gen) | No = No
test' (Exists .(λ x → u)) check (ConsE {u = u} [] gen) = No
test' (Exists .(λ x → u)) check (ConsE {u = u} (x ∷ xs) gen) with test' u (check x) < gen >-iso
test' (Exists ._) check (ConsE (x ∷ xs) gen) | Yes = Yes
test' (Exists ._) check (ConsE (x ∷ xs) gen) | No = test' (Exists _) check (ConsE xs gen)
test' (Property P) (yes p) Nil = Yes
test' (Property P) (no ¬p) Nil = No

open import Data.Empty

test : Testable -> Set
test (C u k input) with test' u k input
test (C u k input) | Yes = Pass
test (C u k input) | No = ⊥       -- TODO collect input

nats : List ℕ
nats = 0 ∷ 1 ∷ []

lists : List (List ℕ)
lists = ([] ∷ nats ∷ [])

test-ex : test (C ex dec-ex {!ConsF nats (ConsE lists Nil) !})
test-ex = {!!}
