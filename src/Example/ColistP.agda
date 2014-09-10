module Example.ColistP where

open import Coinduction
open import Data.Colist using (Colist)
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

-- Does not type check
-- non-productive : Colist ℕ
-- non-productive = ⟦ concatMap (const []) nats' ⟧P

productive : Colist ℕ
productive = ⟦ concatMap (const (1 ∷ (♯ []))) nats' ⟧P
