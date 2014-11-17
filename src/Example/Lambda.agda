-- | Defines an angelic generator for lambda terms of a given type
-- The approach draws from 'Black Box Testing' by Palka

module Example.Lambda where

open import Coinduction
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.List using (List ; [] ; _∷_ ; [_])
import Data.List as L
open import Data.Maybe using (just ; nothing ; Maybe)
import Data.Maybe as M
open import Data.Colist using (Colist ; [] ; _∷_ )
import Data.Colist as C

open import Test.Input.Generator
open import Test.Input.Generator.Base

--------------------------------------------------------------------------------
-- Generators for λ-terms
--------------------------------------------------------------------------------

-- Unit and function types are supported.
data Type : Set where
 O    : Type
 _=>_ : Type -> Type -> Type

-- Generators for types
ty-gen' : ColistP Type
ty-gen' = O ∷ ♯ (concatMap funTy {isProd} ty-gen')
  where funTy : Type -> ColistP Type
        funTy O = (O => O) ∷ (♯ [])
        funTy (ty₁ => ty₂) = (ty₁ => (ty₁ => ty₂)) ∷ (♯ (( (ty₁ => ty₂) => ty₂) ∷ (♯ (((ty₁ => ty₂) => (ty₁ => ty₂)) ∷ ♯ []))))

        isProd : IsProductive funTy
        isProd O = _
        isProd (ty => ty₁) = _

-- | Simple Generator for Types.
ty-gen : SimpleGenerator Type
ty-gen = ⟦ ty-gen' ⟧P

-- | Equality on types is Decidable.
_≟-ty_ : (t1 : Type) -> (t2 : Type) -> Dec (t1 ≡ t2)
O ≟-ty O = yes refl
O ≟-ty (t2 => t3) = no (λ ())
(t1 => t2) ≟-ty O = no (λ ())
(t1 => t2) ≟-ty (t3 => t4) with t1 ≟-ty t3 | t2 ≟-ty t4
(t1 => t2) ≟-ty (.t1 => .t2) | yes refl | yes refl = yes refl
(t1 => t2) ≟-ty (.t1 => t4) | yes refl | no ¬p = no (lemma2 ¬p)
  where lemma2 : ∀ {t1 t2 t3 t4} -> ¬ (t2 ≡ t4) -> (t1 => t2) ≡ (t3 => t4) -> ⊥
        lemma2 ¬p refl = ¬p refl 
(t1 => t2) ≟-ty (t3 => t4) | no ¬p | _ = no (lemma1 ¬p) 
  where lemma1 : ∀ {t1 t2 t3 t4} -> ¬ (t1 ≡ t3) -> (t1 => t2) ≡ (t3 => t4) -> ⊥
        lemma1 ¬p refl = ¬p refl 

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

-- f x y , ∀ x ∈ xs ∀ y ∈ ys  
combine' : ∀ {A B C : Set} -> (f : A -> B -> C) -> List A -> List B -> List C
combine' {A} {B} {C} f xs ys = L.concatMap (λ x → L.map (f x) ys) xs

-- What can be produced via application or lookup in the given context
data Productable (G : Context) (ty : Type) : Set where
  Lookup : Ref G ty -> Productable G ty
  Apply : ∀ {ty'} -> Productable G (ty' => ty) -> Productable G ty' -> Productable G ty

-- | Produces a term of the given type in the given context 
-- from a Productable proof object.
produce : ∀ {G ty} -> Productable G ty -> Term G ty
produce (Lookup x) = Var x
produce (Apply f x) = App (produce f) (produce x)

-- If a term of some type can be produced in some environment, then it
-- can be produced in an increased environment.
lift : ∀ {ty ty' G} -> Productable G ty -> Productable (ty' ∷ G) ty
lift (Lookup x) = Lookup (Pop x)
lift (Apply f x) = Apply (lift f) (lift x)

-- Compact representation of a function that produces ty given the types contained in ts
_==>_ : List Type -> Type -> Type
ts ==> ty = L.foldr _=>_ ty ts

-- | Determines whether a type ty' can produce another type by 0 or more applications.
-- If that is the case those types are collected and returned in a list inside the Maybe monad.
subgoals : (ty ty' : Type) -> Maybe (List Type)
subgoals ty ty' with ty ≟-ty ty'
subgoals ty .ty | yes refl = just []
subgoals ty O | no ¬p = nothing
subgoals ty (ty' => ty'') | no ¬p = M.map (_∷_ ty') (subgoals ty ty'')

-- | Collects in a List all the terms of the given type in the given context.
ref-genL : (G : Context) -> (ty : Type) -> List (Ref G ty)
ref-genL [] i = []
ref-genL (ty₁ ∷ G) ty₂ with ty₁ ≟-ty ty₂
ref-genL (ty₁ ∷ G) .ty₁ | yes refl = Top ∷ (L.map Pop (ref-genL G ty₁))
ref-genL (ty₁ ∷ G) ty₂ | no ¬p = L.map Pop (ref-genL G ty₂)

-- | Angelic generator for reference data-type
ref-gen : (G : Context) -> GeneratorA Type (Ref G)
ref-gen G ty = C.fromList (ref-genL G ty)

-- | Angelic generator for the Productable data type.
-- It returns a List because of productivity issues.
productable-genL : (G : Context) -> (ty : Type) -> List (Productable G ty)
productable-genL G ty = L.concatMap (λ ts → (apply-gen ts (lookup-gen _))) (L.gfilter (subgoals ty) G)
  where lookup-gen : (ty : Type) -> List (Productable G ty)
        lookup-gen ty = L.map Lookup (ref-genL G ty)

        apply-gen : (ts : List Type) -> List (Productable G (ts ==> ty)) -> List (Productable G ty)
        apply-gen [] ps = ps
        apply-gen (ty₁ ∷ []) ps = combine' Apply ps (lookup-gen ty₁)
        apply-gen (ty₁ ∷ ty₂ ∷ ts) ps = apply-gen (ty₂ ∷ ts) (combine' Apply ps xs₁)
          where xs₁ = lookup-gen ty₁

-- | Angelic generator for the Productable data type.
productable-gen : (G : Context) -> GeneratorA Type (Productable G)
productable-gen G ty = C.fromList (productable-genL G ty)

-- | Angelic generator for the λ-terms of the given type in the given context.
term-gen : (G : Context) -> GeneratorA Type (Term G)
term-gen G O = C.map produce (productable-gen G O)
term-gen G (ty₁ => ty₂) = C.map produce (productable-gen G _) C.++ C.map Abs (term-gen (ty₁ ∷ G) ty₂)
