-- Generators in the SmallCheck style

module SmallCheck where


--------------------------------------------------------------------------------
-- Using Reflection
--------------------------------------------------------------------------------
open import Reflection
open import Data.Nat
open import Data.List


-- Depth of a Term
depth : Term -> ℕ
maximum : ℕ -> Arg Term -> List (Arg Term) -> ℕ

depth (var x args) = {!!} -- Could this happen with dependent functions?
depth (con c []) = 0 -- Nullary constructor
depth (con c (arg v r x ∷ args)) = 1 + maximum (depth x) (arg v r x) args -- Positive arity constructor
depth (def f []) = {!!}  
depth (def f (arg v r x ∷ args)) = {!!} -- maximum (depth x) (arg v r x) args
depth (lam v t) = {!!} -- depth t -- Should I take into account visibility? (I don't think so)
depth (pi t₁ t₂) = {!!} -- How to adapt the concept of depth to the π-function space
depth (sort x) = {!!} -- This is related to the above
depth unknown = {!!}

maximum n (arg v r x₁) [] = n ⊔ depth x₁ -- Should I take into account visibility and relevance?
maximum n (arg v₁ r₁ x₁) (arg v₂ r₂ x₂ ∷ args₁) = maximum (n ⊔ (depth x₁)) (arg v₂ r₂ x₂) args₁ 

-- Probably builtin (and primitive) types (String, Int, Floats) are problematic because I think they
-- would end up in unknown. However in common Agda programs they are not as common as ADT.



--------------------------------------------------------------------------------
-- Example from the paper
--------------------------------------------------------------------------------
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Bool

data Name' : Set where
  P Q R : Name'

data Prop' : Set where
  Var : Name' -> Prop'
  Not : Prop' -> Prop'
  Or : Prop' -> Prop' -> Prop'

prop1 : Prop'
prop1 = Or (Not (Var P)) (Var Q)

test1 : depth (quoteTerm prop1) ≡ 3
test1 = refl

-- The two Boolean functions of depth 0
f0₁ : Bool -> Bool
f0₁ _ = true

f0₂ : Bool -> Bool
f0₂ _ = false

-- The four Boolean functions of depth 1
f1₁ : Bool -> Bool
f1₁ true = true
f1₁ false = true

f1₂ : Bool -> Bool
f1₂ true = true
f1₂ false = false

f1₃ : Bool -> Bool
f1₃ true = false
f1₃ false = true 

f1₄ : Bool -> Bool
f1₄ true = false
f1₄ false = false

-- I think that the difference between these two cases is that in the f0₁
-- the function is beta reduced because the argument is not inspected.

test2 : depth (quoteTerm f0₁ ) ≡ 0
test2 = {!!}

test4 : depth (quoteTerm f1₁ ) ≡ 1
test4 = {!!}

--------------------------------------------------------------------------------
-- Using Regular :
--------------------------------------------------------------------------------

open import Data.Unit
open import Data.Sum hiding (map)
open import Data.Product hiding (map)
open import Data.Nat

record Serial (A : Set) : Set₁ where
  constructor Gen 
  field 
    series : ℕ -> List A

-- Code + Generator
data Regular : Set₁ where
  U    :                      Regular
  K    : (A : Set) -> Serial A ->  Regular
  _⊕_  : (F G : Regular)  ->  Regular
  _⊗_  : (F G : Regular)  ->  Regular
  I    :                      Regular

-- Interpretation
⟦_⟧ : Regular -> Set -> Set
⟦ U      ⟧ r = ⊤
⟦ K a _  ⟧ r = a
⟦ F ⊕ G  ⟧ r = ⟦ F ⟧ r ⊎ ⟦ G ⟧ r
⟦ F ⊗ G  ⟧ r = ⟦ F ⟧ r × ⟦ G ⟧ r
⟦ I      ⟧ r = r

-- Fixpoint
data µ (F : Regular) : Set where
  ⟨_⟩ : ⟦ F ⟧ (µ F) -> µ F

-- The user (or automatically using reflection) defines an isomorphism 
-- from the data types involved in the properties to Regular.
-- Regular data types are generated and then mapped back to the user-defined type.

record Isomorphism (A : Set) : Set₁ where
  constructor Iso
  field 
    C : Regular
    from : A -> ⟦ C ⟧ A
    to   : ⟦ C ⟧ A -> A
-- Returns the depth of a Regular data type
-- Problem : We cannot write this function directly for a generic A, because PF is abstract.
-- depth : ∀ {A} -> Isomorphism A -> A -> ℕ
-- depth (Iso PF from to) a with from a
-- ... | r = {!!}

Depth : Set
Depth = ℕ 

interleave : {A : Set} -> List A -> List A -> List A 
interleave [] ys = ys
interleave (x ∷ xs) (y ∷ ys) = x ∷ y ∷ interleave xs ys
interleave xs [] = xs

gSeries : ∀ {r} -> (C : Regular) -> Depth -> List ( ⟦ C ⟧ r )
gSeries U n = [ tt ]
gSeries (K A (Gen series)) n = series n
gSeries (C ⊕ C₁) zero = []
gSeries {r} (C ⊕ C₁) (suc n) =
  let ls = map inj₁ (gSeries {r} C n)
      rs = map inj₂ (gSeries {r} C₁ n) in
  interleave ls rs
gSeries {r} (C ⊗ C₁) n = zipWith _,_ (gSeries {r} C n) (gSeries {r} C₁ n)
gSeries I n = {!!} -- Should I use the fixpoint ? How ?

series : ∀ {A} -> Isomorphism A -> Depth -> List A
series {A} (Iso C from to) depth = map to (gSeries {A} C depth)

--------------------------------------------------------------------------------
-- Examples
--------------------------------------------------------------------------------
  
open import Data.Nat
open import Relation.Binary.PropositionalEquality

NatC : Regular
NatC = U ⊕ I

aNat : µ NatC
aNat = ⟨ inj₂ ⟨ inj₂ ⟨ inj₁ tt ⟩ ⟩ ⟩

fromℕ : ℕ -> ⟦ NatC ⟧ ℕ
fromℕ zero = inj₁ tt
fromℕ (suc n) = inj₂ n

toℕ : ⟦ NatC ⟧ ℕ -> ℕ
toℕ (inj₁ tt) = zero
toℕ (inj₂ n) = suc n

sanity-check' : ∀ (n : ℕ) -> (toℕ (fromℕ n)) ≡ n
sanity-check' zero = refl
sanity-check' (suc n) = refl 

isoℕ : Isomorphism ℕ
isoℕ = Iso NatC fromℕ toℕ

--------------------------------------------------------------------------------
-- In Haskell I need a pattern functor because I don't have dependent types?
-- It is the machinery in the compiler that makes it work

-- TODO Shall I require the proof of the isomorphism? 
record Isomorphism' (A : Set) : Set₁ where
  constructor Iso'
  field
    PF   : Set -> Set -> Set
    from : A -> PF A A 
    to   : PF A A -> A


PFℕ : Set -> Set -> Set
PFℕ ℕ = ⟦ U ⊕ I ⟧

-- Iso for ℕ
fromℕ' : ℕ -> PFℕ ℕ ℕ 
fromℕ' zero = inj₁ tt
fromℕ' (suc t) = inj₂ t

toℕ' : PFℕ ℕ ℕ -> ℕ 
toℕ' (inj₁ x) = zero
toℕ' (inj₂ y) = suc y

isoℕ' : Isomorphism' ℕ
isoℕ' = Iso' PFℕ fromℕ toℕ

-- Sanity check
isoℕ-proof : ∀ n -> toℕ (fromℕ n) ≡ n
isoℕ-proof zero = refl
isoℕ-proof (suc n) = refl 
