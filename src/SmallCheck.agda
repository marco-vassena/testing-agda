-- Generators in the SmallCheck style

module SmallCheck where

open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.Nat

-- Code
data Regular : Set₁ where
  U    :                      Regular
  K    : (A : Set)        ->  Regular
  _⊕_  : (F G : Regular)  ->  Regular
  _⊗_  : (F G : Regular)  ->  Regular
  I    :                      Regular

-- Interpretation
⟦_⟧ : Regular -> Set -> Set
⟦ U      ⟧ r = ⊤
⟦ K a    ⟧ r = a
⟦ F ⊕ G  ⟧ r = ⟦ F ⟧ r ⊎ ⟦ G ⟧ r
⟦ F ⊗ G  ⟧ r = ⟦ F ⟧ r × ⟦ G ⟧ r
⟦ I      ⟧ r = r

-- Fixpoint
data µ (F : Regular) : Set where
  ⟨_⟩ : ⟦ F ⟧ (µ F) -> µ F


-- The user (or automatically using reflection) defines an isomorphism 
-- from the data types involved in the properties to Regular.
-- Regular data types are generated and then mapped back to the user-defined type.

-- TODO Shall I require the proof of the isomorphism? 
record Isomorphism (A : Set) : Set₁ where
  constructor Iso
  field
    PF   : Set -> Set -> Set
    from : A -> PF A A 
    to   : PF A A -> A

-- Returns the depth of a Regular data type
-- Problem : We cannot write this function directly for a generic A, because PF is abstract.

-- depth : ∀ {A} -> Isomorphism A -> A -> ℕ
-- depth (Iso PF from to) a with from a
-- ... | r = {!!}

depth' : Regular -> ℕ
depth' r with ⟦ r ⟧
... | p = {!!}

--------------------------------------------------------------------------------
-- Examples
--------------------------------------------------------------------------------
  
open import Data.Nat
open import Relation.Binary.PropositionalEquality

PFℕ : Set -> Set -> Set
PFℕ ℕ = ⟦ U ⊕ I ⟧

-- Iso for ℕ
fromℕ : ℕ -> PFℕ ℕ ℕ 
fromℕ zero = inj₁ tt
fromℕ (suc t) = inj₂ t

toℕ : PFℕ ℕ ℕ -> ℕ 
toℕ (inj₁ x) = zero
toℕ (inj₂ y) = suc y

isoℕ : Isomorphism ℕ
isoℕ = Iso PFℕ fromℕ toℕ

-- Sanity check
isoℕ-proof : ∀ n -> toℕ (fromℕ n) ≡ n
isoℕ-proof zero = refl
isoℕ-proof (suc n) = refl 

