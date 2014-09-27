module Example.ColistP where

open import Coinduction
open import Data.Colist using (Colist ; [] ; _∷_)
open import Data.Nat
open import Function
open import Test.Input.Generator.Base

fibP : ColistP ℕ
fibP = 0 ∷ ♯ zipWith _+_ fibP (1 ∷ ♯ fibP)

fib : Colist ℕ
fib = ⟦ fibP ⟧P 

append : Colist ℕ
append = ⟦ xs ++ ys ⟧P
  where xs ys : ColistP ℕ
        xs = 1 ∷ ♯ (2 ∷ (♯ (3 ∷ (♯ []))))
        ys = 4 ∷ ♯ (5 ∷ (♯ (6 ∷ (♯ []))))

nats' : ColistP ℕ
nats' = 0 ∷ ♯ (map suc nats')

nats : Colist ℕ
nats = ⟦ nats' ⟧P

-- Does not type check because const [] is not productive
-- non-productive : Colist ℕ
-- non-productive = ⟦ concatMap (const []) nats' ⟧P

productive : Colist ℕ
productive = ⟦ concatMap (const (1 ∷ (♯ []))) nats' ⟧P

-- Examples with Prod data-type

example : ∀ {A B} -> Prod {A = A} {B = B} (const []) []
example = Base

open import Example.Even using (isEven? ; Even)
open import Relation.Nullary

evens : ℕ -> Colist ℕ
evens n with isEven? n
evens n | yes p = n ∷ (♯ [])
evens n | no ¬p = [] 

open import Relation.Binary.PropositionalEquality

ones : ColistP ℕ
ones = 1 ∷ ♯ ones

ones-prod : Prod (λ n → n ∷ ♯ []) ones
ones-prod = Now (♯ ones-prod) (λ z → z)

ex1 : Prod {!!} {!!}
ex1 = {!Now ? ?!}

open import Data.Bool

-- Even n if on true, ¬ Even otherwise
evenOrOdd : Bool -> (n : ℕ) -> Set
evenOrOdd true n = Even n
evenOrOdd false n = ¬ Even n

-- An interchanged sequence of even and odd numbers 
data EvenOddSeqence : Bool -> Colist ℕ -> Set where
  [] : ∀ {b} -> EvenOddSeqence b []
  _∷_ : ∀ {b ns} -> (n : ℕ) -> {p : evenOrOdd b n} -> ∞ (EvenOddSeqence (not b) (♭ ns)) -> EvenOddSeqence b (n ∷ ns)

nats-even-odd : EvenOddSeqence true nats
nats-even-odd = _∷_ zero {Example.Even.isEven0} (♯ (_∷_ (suc zero) {λ ()} (♯ (_∷_ (suc (suc zero)) {Example.Even.isEven+2 Example.Even.isEven0} (♯ {!!})))))

even : ∀ {ns} -> EvenOddSeqence true ns -> Prod' evens ns
odd : ∀ {ns} -> EvenOddSeqence false ns -> Prod' evens ns
even [] = Base
even (_∷_ n {p} ns) = Now (♯ (odd (♭ ns))) (f n p)
  where f : ∀ n -> Even n -> Cons (evens n)
        f .0 Example.Even.isEven0 = _
        f (suc (suc n)) (Example.Even.isEven+2 p) with evens (suc (suc n)) | isEven? (suc (suc n))
        f (suc (suc n)) (Example.Even.isEven+2 p₁) | [] | yes p = _
        f (suc (suc n)) (Example.Even.isEven+2 p) | [] | no ¬p = ¬p (Example.Even.isEven+2 p)
        f (suc (suc n₁)) (Example.Even.isEven+2 p₁) | x ∷ xs | yes p = _
        f (suc (suc n₁)) (Example.Even.isEven+2 p) | x ∷ xs | no ¬p = ¬p (Example.Even.isEven+2 p) 
odd [] = Base
odd (n ∷ ns) = Skip (even (♭ ns))

ex2' : ∀ {b ns} -> EvenOddSeqence b ns -> Prod' evens ns
ex2' [] = Base
ex2' (_∷_ {true} n {p} ns) = even (_∷_ {true} n {p} ns)
ex2' (_∷_ {false} n {p} ns) = odd (_∷_ {false} n {p} ns)

-- Improductive
g : ∀ {A : Set} -> A -> ColistP ℕ
g = const []

ex3 : NonProd g nats'
ex3 = go nats'
  where go : (xs : ColistP ℕ) -> NonProd g xs
        go xs = {!!}
