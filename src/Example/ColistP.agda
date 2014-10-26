module Example.ColistP where

open import Coinduction
open import Data.Colist using (Colist ; [] ; _∷_ ; _≈_)
open import Data.Nat
open import Function
open import Test.Input.Generator.Base

--------------------------------------------------------------------------------
-- Example with IsProductive
--------------------------------------------------------------------------------

fib : Colist ℕ
fib = ⟦ fibP ⟧P 
  where fibP : ColistP ℕ
        fibP = 0 ∷ ♯ zipWith _+_ fibP (1 ∷ ♯ fibP)

nats' : ColistP ℕ
nats' = iterate suc zero

nats : Colist ℕ
nats = ⟦ nats' ⟧P

-- Does not type check because const [] is not productive
-- non-productive : Colist ℕ
-- non-productive = ⟦ concatMap (const []) nats' ⟧P

productive : Colist ℕ
productive = ⟦ concatMap (const (1 ∷ (♯ []))) nats' ⟧P

--------------------------------------------------------------------------------
-- Examples with Prod data-type
--------------------------------------------------------------------------------

ones : Colist ℕ
ones = 1 ∷ ♯ ones

ones-prod : Prod (λ n → n ∷ ♯ []) ones
ones-prod = Now (♯ ones-prod) _

open import Example.Even using (isEven? ; Even ; isEven0 ; isEven+2)
open import Relation.Nullary
open import Data.Bool

evens : ℕ -> Colist ℕ
evens n with isEven? n
evens n | yes p = n ∷ (♯ [])
evens n | no ¬p = [] 

-- Even n if on true, ¬ Even otherwise
evenOrOdd : Bool -> (n : ℕ) -> Set
evenOrOdd true n = Even n
evenOrOdd false n = ¬ Even n

-- An interchanged sequence of even and odd numbers 
data EvenOddSeqence : Bool -> Colist ℕ -> Set where
  [] : ∀ {b} -> EvenOddSeqence b []
  _∷_ : ∀ {b ns} -> (n : ℕ) -> {p : evenOrOdd b n} -> ∞ (EvenOddSeqence (not b) (♭ ns)) -> EvenOddSeqence b (n ∷ ns)

open import Data.Empty using (⊥-elim)
open import Data.Sum using (inj₁ ; inj₂ ; _⊎_)
import Data.Sum as S
          
even : ∀ {ns} -> EvenOddSeqence true ns -> Prod evens ns
odd : ∀ {ns} -> EvenOddSeqence false ns -> Prod evens ns
even [] = Base
even (_∷_ n {p} ns) = Now (♯ (odd (♭ ns))) (even2NonNull p) 
  where even2NonNull : ∀ {n} -> Even n -> NonNull (evens n)
        even2NonNull isEven0 = _
        even2NonNull {.(suc (suc n))} (isEven+2 {n} p) with isEven? n
        even2NonNull (isEven+2 p) | yes _ = _
        even2NonNull (isEven+2 p) | no ¬p = ¬p p

odd [] = Base
odd (n ∷ ns) = Skip (even (♭ ns))

-- evens is productive if applied on any EvenOddSequence, nats included
evens-prod : ∀ {b ns} -> EvenOddSeqence b ns -> Prod evens ns
evens-prod {true} seq = even seq
evens-prod {false} seq = odd seq

-- | If n is Even then suc n is not Even
even-next-odd : ∀ {n} -> Even n -> ¬ (Even (suc n))
even-next-odd isEven0 ()
even-next-odd (isEven+2 p) (isEven+2 x) = even-next-odd p x

-- | Either n is Even or suc n is Even
this-or-next : ∀ n -> (Even n) ⊎ (Even (suc n))
this-or-next zero = inj₁ isEven0
this-or-next (suc n) with this-or-next n
this-or-next (suc n₁) | inj₁ x = inj₂ (isEven+2 x)
this-or-next (suc n₁) | inj₂ y = inj₁ y

-- | If n is not Even then suc n is Even
odd-next-even : ∀ {n} -> (¬ Even n) -> Even (suc n)
odd-next-even {n} ¬p with this-or-next n
odd-next-even ¬p | inj₁ p = ⊥-elim (¬p p)
odd-next-even ¬p | inj₂ p = p

-- Proof that nats it's an EvenOddSeqence 
nats-even-odd : EvenOddSeqence true nats
nats-even-odd = proof 0 isEven0
  where proof : ∀ {b} -> (n : ℕ) -> evenOrOdd b n -> EvenOddSeqence b (⟦ iterate suc n ⟧P)
        proof {true} n p = _∷_ n {p} (♯ (proof (suc n) (even-next-odd p)))
        proof {false} n p = _∷_ n {p} (♯ (proof (suc n) (odd-next-even p)))

-- After all those proofs we can write:
-- [0, 2, 4, 6 ...]
example₁ : Colist ℕ
example₁ = concatMapC evens nats {isP}
  where isP : Prod evens nats
        isP = evens-prod nats-even-odd

--------------------------------------------------------------------------------
-- Examples with self-generative colist
--------------------------------------------------------------------------------

-- foo = 0 ∷ ♯ (concatMap f foo)
foo : ColistP ℕ
foo = ⟦ Input f (0 ∷ []) ⟧SG
  where f : ℕ -> ColistP ℕ
        f n = (n + 1) ∷ (♯ ((n + 3) ∷ ♯ []))


-- bar n = n ∷ ♯ (concatMap count (bar n))
-- This term would eventually be looping using concatMap
-- Here it terminates gracefully
bar : ℕ -> ColistP  ℕ
bar n = ⟦ Input₁ count n ⟧SG
  where count : ℕ -> ColistP ℕ
        count zero = []
        count (suc n₁) = n₁ ∷ ♯ (count n₁)
