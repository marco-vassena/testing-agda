-- | This module defines an automatic converter able to 
-- produce the correspondent 'Predicate' given a lemma's type.

module Test.Converter where

open import Test.Base

open import Reflection
open import Data.List hiding (or ; and)

--------------------------------------------------------------------------------
-- Term level constructor
--------------------------------------------------------------------------------

private
  property : Term -> Term
  property p = con (quote Property) [ argp ]
    where argp = arg (arg-info visible relevant) p

  forall' : Term -> Term -> Term
  forall' ty next = con (quote Predicate.Forall) (argTy ∷ argNext ∷ [])
    where argTy = arg (arg-info hidden relevant) ty
          argNext = arg (arg-info visible relevant) (lam visible (abs "x" next))

  not : Term -> Term
  not next = con (quote Not) [ argNext ]
    where argNext = arg (arg-info visible relevant) next

  or : Term -> Term -> Term
  or t1 t2 = con (quote _∨_) (arg1 ∷ arg2 ∷ [])
    where arg1 = arg (arg-info visible relevant) t1
          arg2 = arg (arg-info visible relevant) t2

  and : Term -> Term -> Term
  and t1 t2 = def (quote _∧_) (arg1 ∷ arg2 ∷ [])
    where arg1 = arg (arg-info visible relevant) t1
          arg2 = arg (arg-info visible relevant) t2

  exists : (t : Term) -> Term
  exists t = con (quote Predicate.Exists) [ arg1 ]
    where arg1 = arg (arg-info visible relevant) (lam visible (abs "x" t))

--------------------------------------------------------------------------------
-- -- Conversion error messages
--------------------------------------------------------------------------------
data NotSupported : Term -> Set where

--------------------------------------------------------------------------------
-- Support functions
-- Type level functions that determine whether automatic conversion is possible.
--------------------------------------------------------------------------------

open import Data.Product
open import Data.Maybe
open import Data.Sum
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Data.Empty
open import Data.Nat
open import Data.Unit

private
  -- | Checks if the given 'Term' can be automatically converted
  supportedTerm : Term -> Set

  data Special : Term -> Set where
    Or : ∀ {x₁ x₂ x₃ x₄} -> Special (def (quote _⊎_) (x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ []))
    Not : ∀ {i s ty s₁ s₂} -> Special (pi (arg i (el s ty)) (abs s₁ (el s₂ ((def (quote ⊥) [])))))
    Exists : ∀ {x₁ x₂ x₃ i f args} -> Special (def (quote Σ) (x₁ ∷ x₂ ∷ x₃ ∷ arg i (def f args) ∷ []))
    And : ∀ {x₁ x₂ x₃ i v t} -> Special ((def (quote Σ) (x₁ ∷ x₂ ∷ x₃ ∷ arg i (lam v t) ∷ [])))

  isSpecial : (t : Term) -> Maybe (Special t)
  isSpecial (def f args) with f ≟-Name (quote Σ)
  isSpecial (def .(quote Σ) (x₁ ∷ x₂ ∷ x₃ ∷ arg i (def f args) ∷ [])) | yes refl = just Exists
  isSpecial (def .(quote Σ) (x₁ ∷ x₂ ∷ x₃ ∷ arg i (lam v t) ∷ [])) | yes refl = just And
  isSpecial (def f _) | yes p = nothing
  isSpecial (def f args) | no ¬p with f ≟-Name (quote _⊎_)
  isSpecial (def .(quote _⊎_) (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ [])) | no ¬p | yes refl = just Or
  isSpecial (def .(quote _⊎_) _) | no ¬p | yes refl = nothing
  isSpecial (def f args) | no ¬p₁ | no ¬p = nothing 
  isSpecial (pi t₁ (abs s₁ (el s₂ (def f [])))) with f ≟-Name (quote ⊥)
  isSpecial (pi (arg i (el s t)) (abs s₁ (el s₂ (def .(quote ⊥) [])))) | yes refl = just Not
  isSpecial (pi t₁ (abs s₁ (el s₂ (def f [])))) | no ¬p = nothing
  isSpecial (pi _ _) = nothing
  isSpecial _ = nothing


  -- | Lower the De Brujin indexes of the given term by one position.
  -- The goal is to correct the indices for the function introduced by ∑ (indirectly by ×). 
  fixIndices : Term -> Term
  fixSortIndices : Sort -> Sort
  fixTypeIndices : Type -> Type
  fixArgTermIndices : List (Arg Term) -> List (Arg Term)

  fixSortIndices (set t) = set (fixIndices t)
  fixSortIndices (lit n) = lit n
  fixSortIndices unknown = unknown
  
  fixTypeIndices (el s t) = el (fixSortIndices s) (fixIndices t)
  
  fixArgTermIndices [] = []
  fixArgTermIndices (arg i x ∷ args) = (arg i (fixIndices x)) ∷ (fixArgTermIndices args)

  fixClauseIndices : List Clause -> List Clause
  fixClauseIndices [] = []
  fixClauseIndices (clause pats body ∷ xs) = (clause pats (fixIndices body)) ∷ (fixClauseIndices xs)
  fixClauseIndices (absurd-clause pats ∷ xs) = (absurd-clause pats) ∷ (fixClauseIndices xs)

  fixIndices (var x args) = var (x ∸ 1) (fixArgTermIndices args)
  fixIndices (con c args) = con c (fixArgTermIndices args)
  fixIndices (def f args) = def f (fixArgTermIndices args)
  fixIndices (lam v (abs s x)) = lam v (abs s (fixIndices x))
  fixIndices (pat-lam cs args) = pat-lam (fixClauseIndices cs) (fixArgTermIndices args)
  fixIndices (pi (arg i ty) (abs s₁ t₂)) = pi (arg i (fixTypeIndices t₂)) (abs s₁ (fixTypeIndices t₂))
  fixIndices (sort s) = sort (fixSortIndices s)
  fixIndices (lit l) = lit l
  fixIndices unknown = unknown

  supportedTerm t with isSpecial t
  supportedTerm ._ | just (Or {x₃ = arg i₁ x₁} {x₄ = arg i₂ x₂}) = (supportedTerm x₁) × (supportedTerm x₂) 
  supportedTerm ._ | just (Not {ty = ty}) = supportedTerm ty
  supportedTerm ._ | just (Exists {f = f} {args = args}) = supportedTerm (def f args)
  supportedTerm ._ | just (And {x₃ = arg i t₁} {t = abs s t₂}) = (supportedTerm t₁) × (supportedTerm t₂)
  supportedTerm (var x args) | nothing = NotSupported (var x args)
  supportedTerm (con c args) | nothing = NotSupported (con c args)
  supportedTerm (def f args) | nothing = ⊤
  supportedTerm (lam v (abs s x)) | nothing = supportedTerm x
  supportedTerm (pat-lam cs args) | nothing = NotSupported (pat-lam cs args)
  supportedTerm (pi t₁ (abs s₁ (el s₂ t₂))) | nothing = supportedTerm t₂
  supportedTerm (sort s) | nothing = NotSupported (sort s)
  supportedTerm (lit l) | nothing = ⊤
  supportedTerm unknown | nothing = NotSupported unknown

supported : Type -> Set
supported (el s t) = supportedTerm t

--------------------------------------------------------------------------------
-- Conversion
-- These functions produce a 'Term' that when unquoted gives the
-- correspondent property.
--------------------------------------------------------------------------------

private
  convertTerm : (t : Term) -> {isSup : supportedTerm t} -> Term
  convertTerm t {isS} with isSpecial t
  convertTerm ._ {isS₁ , isS₂} | just (Or {x₃ = arg i₁ x₁} {arg i₂ x₂}) = or (convertTerm x₁ {isS₁}) (convertTerm x₂ {isS₂})
  convertTerm ._ {isS} | just (Not {ty = ty}) = not (convertTerm ty {isS})
  convertTerm ._ {isS} | just (Exists {f = f} {args = args}) = exists (convertTerm (def f args) {isS})
  convertTerm ._ {isS₁ , isS₂} | just (And {x₃ = arg i t₁} {t = abs s t₂}) = and (convertTerm t₁ {isS₁}) (fixIndices (convertTerm t₂ {isS₂}))
  convertTerm (var x args) {} | nothing
  convertTerm (con c args) {} | nothing
  convertTerm (def f args) {isS} | nothing = property (def f args)
  convertTerm (lam v (abs s x)) {isS} | nothing = convertTerm x {isS}
  convertTerm (pat-lam cs args) {} | nothing
  convertTerm (pi (arg i (el s ty)) (abs s₁ (el s₂ t))) {isS} | nothing = forall' ty (convertTerm t {isS})
  convertTerm (sort s) {} | nothing
  convertTerm (lit l) | nothing = lit l 
  convertTerm unknown {} | nothing

convert : (name' : Name) -> {isSup : supported (type name')} -> Term
convert name' {isS} with type name'
convert name' {isS} | el s t = convertTerm t {isS}
