module Example.ColistP where

open import Coinduction
open import Data.Colist using (Colist ; [] ; _∷_ ; _≈_)
open import Data.Nat
open import Function
open import Test.Input.Generator.Base
open import Data.Unit
open import Relation.Nullary

-- | Productive definition of the fibonacci series.
fib : Colist ℕ
fib = ⟦ fibP ⟧P
  where fibP : ColistP ℕ
        fibP = 0 ∷ ♯ zipWith _+_ fibP (1 ∷ ♯ fibP)

natsP : ColistP ℕ
natsP = iterate suc zero

nats : Colist ℕ
nats = ⟦ natsP ⟧P

--------------------------------------------------------------------------------
-- Example with IsProductive
--------------------------------------------------------------------------------

-- If a function is productive (never returns an empty colist), its IsProductive 'proof'
-- typically follows the definition of the function.
-- Consider wrap as an example: 

data A : Set where
  B : A
  C : A

wrap : A -> ColistP A
wrap B = B ∷ ♯ []
wrap C = C ∷ ♯ []

productive-wrap : IsProductive wrap
productive-wrap B = tt
productive-wrap C = tt

--------------------------------------------------------------------------------
-- An example of non productive function

empty : ℕ -> ColistP ℕ
empty = const []

empty-non-prod : ¬ (IsProductive empty)
empty-non-prod p = p 0  -- A counter example

-- Does not type check because empty is not productive
-- non-productive : Colist ℕ
-- non-productive = ⟦ concatMap empty natsP ⟧P

-- Another example
maybe-wrap : A -> ColistP A
maybe-wrap B = []
maybe-wrap C = C ∷ ♯ []

maybe-wrap-non-prod : ¬ (IsProductive maybe-wrap)
maybe-wrap-non-prod p = p B -- the only counter example

--------------------------------------------------------------------------------
-- | Sometimes IsProductive can be automatically inferred, as it happens here.
one : ℕ -> ColistP ℕ 
one = const (1 ∷ (♯ []))

productive : Colist ℕ
productive = ⟦ concatMap one natsP ⟧P

--------------------------------------------------------------------------------
-- Examples with Prod data-type
--------------------------------------------------------------------------------

ones : Colist ℕ
ones = 1 ∷ ♯ ones

singleton : ℕ -> Colist ℕ
singleton n = n ∷ ♯ []

-- The proof it's very easy in this case, because singleton itself is productive
singleton-prod : ∀ xs -> Prod singleton xs
singleton-prod [] = Base
singleton-prod (x ∷ xs) = Now (♯ (singleton-prod (♭ xs))) _

-- concatMap singleton ones is productive
ones-prod : Prod singleton ones
ones-prod = singleton-prod ones

--------------------------------------------------------------------------------
-- A more involved example, in which
-- it's not trivial to proof the productivity.

open import Example.Even using (isEven? ; Even ; isEven0 ; isEven+2)
open import Relation.Nullary
open import Data.Bool

-- A function that returns an empty colist for odd numbers 
evens : ℕ -> Colist ℕ
evens n with isEven? n
evens n | yes p = n ∷ (♯ [])
evens n | no ¬p = [] 

-- concatMap evens xs it's in general non productive.
-- Therefore we model colists for which it is productive.
-- To keep it simple here we consider a colist of numbers alternatively even.

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

-- Auxiliary proofs: they handle both cases of EvenOddSequences starting either with an odd or an even.
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
this-or-next (suc zero) = inj₂ (isEven+2 isEven0)
this-or-next (suc (suc n)) with this-or-next n
this-or-next (suc (suc n)) | inj₁ x = inj₁ (isEven+2 x)
this-or-next (suc (suc n)) | inj₂ y = inj₂ (isEven+2 y)

--  with this-or-next n
-- this-or-next (suc n₁) | inj₁ x = inj₂ (isEven+2 x)
-- this-or-next (suc n₁) | inj₂ y = inj₁ y

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
-- Note that no proof is required because a well-defined total semantics 
-- is given to ⟦_⟧SG.
-- Precisely any well-behaved definition is equivalently produced by ⟦_⟧SG (infinite colists)
-- For a looping definition ⟦_⟧SG will produce a finite colist.
--------------------------------------------------------------------------------

-- foo = 0 ∷ ♯ (concatMap f foo)
foo : ColistP ℕ
foo = ⟦ Input f (0 ∷ []) ⟧SG
  where f : ℕ -> ColistP ℕ
        f n = (n + 1) ∷ (♯ ((n + 3) ∷ ♯ []))


-- bar n = n ∷ ♯ (concatMap count (bar n))
-- Depending on n this term would eventually be looping using concatMap directly.
-- Here it terminates gracefully producing a finite colist.
bar : ℕ -> ColistP  ℕ
bar n = ⟦ Input₁ count n ⟧SG
  where count : ℕ -> ColistP ℕ
        count zero = []
        count (suc n₁) = n₁ ∷ ♯ (count n₁)
