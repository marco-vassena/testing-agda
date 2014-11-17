module Test.Input.Generator where

open import Data.Colist
open import Data.Product using (∃ ; _,_ ; _×_ ; proj₁)
open import Function
open import Coinduction

--------------------------------------------------------------------------------
-- Generator interfaces
--------------------------------------------------------------------------------

-- | Generator for non dependent types
SimpleGenerator : Set -> Set
SimpleGenerator A = Colist A

-- | Generators for dependent types
-- Angelic interface : the user chooses the index
GeneratorA : (I : Set) -> (p : (i : I) -> Set) -> Set
GeneratorA I p = ∀ (i : I) -> Colist (p i)

-- | Generators for dependent types
-- Demoniac interface : the index may vary arbitrarily
GeneratorD : (I : Set) -> (p : (i : I) -> Set) -> Set
GeneratorD I p = Colist (∃ p)

-- | Collects the input values (in which we are ultimately interested) from a Colist
-- of proof objects
collect : ∀ {I : Set} {p : I -> Set} ->  GeneratorD I p -> Colist I
collect xs = map proj₁ xs
