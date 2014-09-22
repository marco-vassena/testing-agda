module Test.Input.Generator where

open import Data.Colist
open import Data.Product using (∃ ; _,_ ; _×_)
open import Function
open import Coinduction

--------------------------------------------------------------------------------
-- Data type for generator
--------------------------------------------------------------------------------
-- TODO move to new module

-- Stream vs Colist
-- I would choose for CoList
--   some enumeration are inherently finite
--   some are empty
-- But still we might want to model those

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

-- Angelic  version
GeneratorA : (I : Set) -> (p : (i : I) -> Set) -> Set
GeneratorA I p = ∀ (i : I) -> Colist (p i)

-- Demoniac version
GeneratorD : (I : Set) -> (p : (i : I) -> Set) -> Set
GeneratorD I p = Colist (∃ p)

-- | Collects the input values (in which we are ultimately interested) from a Colist
-- of proof objects
collect : ∀ {I : Set} {p : I -> Set} ->  GeneratorD I p -> Colist I
collect [] = []
collect ((i , _) ∷ xs) = i ∷ ♯ (collect (♭ xs))

-- TODO remove?
-- | This is actually not really useful because of the signature of f.
-- It's rare that for any I the property p holds.
-- Choosing I such that f is trivial is not an option
generate : {I : Set} -> {p : I -> Set} -> (f : ∀ (i : I) -> p i) -> Colist I -> GeneratorD I p
generate f [] = []
generate f (x ∷ xs) = (x , (f x)) ∷ (♯ (generate f (♭ xs)))

-- TODO combinators for dealing with generation of multiple values

-- GeneratorD for non dependent types
SimpleGenerator : Set -> Set
SimpleGenerator A = Colist A

-- Generator for non-dependent types
-- Alternative definition ... same shape as GeneratorD
-- SimpleGenerator : Set-> Set
-- SimpleGenerator A = GeneratorD A (const A)

open import Test.Input.Generator.Base
open import Data.Product using (,_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Binary

-- angelic2demoniac : ∀ {I P} -> SimpleGenerator I -> GeneratorA I P -> GeneratorD I P
-- angelic2demoniac [] a = []
-- angelic2demoniac {I} {P} (x ∷ xs) a = ⟦ d ⟧P 
--   where pack : I -> ColistP (∃ P)
--         pack x = ColistP.map ,_ (fromColist (a x))

--         -- IsProductive proof for GeneratorA is very restrictive (e.g. even-gen)
--         -- Alternatives ?
--         d : ColistP (∃ P)
--         d = concatMap pack {{!!}} (fromColist (x ∷ xs))

-- demoniac2angelic : ∀ {I P} -> {_≟_ : (Decidable (_≡_ {_} {I})) } -> GeneratorD I P -> GeneratorA I P
-- demoniac2angelic [] i = []
-- demoniac2angelic {_≟_ = _≟_} ((i₁ , p) ∷ xs) i₂ with i₁ ≟ i₂
-- demoniac2angelic {_≟_ = _≟_} ((i₁ , p) ∷ xs) .i₁ | yes refl = p ∷ ♯ (demoniac2angelic {_≟_ = _≟_} (♭ xs) i₁)
-- demoniac2angelic {_≟_ = _≟_} ((i₁ , p) ∷ xs) i₂ | no ¬p = demoniac2angelic {_≟_ = _≟_} (♭ xs) i₂ -- Possibly non-terminating
