
module Algebra.Prime where

--------------------------------------------------------------------------------

open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties

open import Relation.Binary.PropositionalEquality

--------------------------------------------------------------------------------

IsOdd : (n : ℕ) -> {NonZero n} -> Set
IsOdd n = (n % 2 ≡ 1)

record Prime : Set where
  constructor MkPrime
  field
    primeℕ    : ℕ 
    isNonZero : NonZero primeℕ
    isOdd     : IsOdd   primeℕ {isNonZero}

--------------------------------------------------------------------------------

private 

  {-# NON_COVERING #-}
  prove-nonZero : (n : ℕ) -> NonZero n
  prove-nonZero (suc n₁) = ≢-nonZero absurd where
    absurd : suc n₁ ≡ zero -> ⊥
    absurd ()

  {-# NON_COVERING #-}
  prove-odd : (n : ℕ) -> {nz : NonZero n} -> IsOdd n {nz}
  prove-odd n {nz} with n % 2
  prove-odd n {nz} | 1 = refl

--------------------------------------------------------------------------------

mkPrime : ℕ -> Prime
mkPrime p = MkPrime p nz odd where
  nz  = prove-nonZero p
  odd = prove-odd     p {nz} 

--------------------------------------------------------------------------------
