
-- NOTE: we use the convention `(hi , lo)`
--
-- This is a rather questionable design choice, which I may change later,
-- but currently seems somewhat more consistent this way
--

module Algebra.U128 where

--------------------------------------------------------------------------------

open import Data.Nat      using ( ℕ ) renaming ( zero to nzero ; suc to nsuc )
open import Data.Nat.Show using ( show )
open import Data.String   using ( String ; _++_ )
open import Data.Fin      using ( Fin ; opposite ) renaming ( zero to fzero ; suc to fsuc )
open import Data.List
open import Data.Word64   using ( fromℕ )
open import Data.Product

open import Meta.HList
open import Meta.Object

open BitLib
open U64Lib

--------------------------------------------------------------------------------

zeroU128 : Tm U128
zeroU128 = mkPair zeroU64 zeroU64

smallU128 : Tm U64 -> Tm U128
smallU128 lo = mkPair zeroU64 lo

addCarryU128 : Tm Bit -> Tm U128 -> Tm U128 -> Tm (Pair Bit U128)
addCarryU128 c₀ x y = runGen do
  (xhi , xlo) ← pair⇑ x
  (yhi , ylo) ← pair⇑ y
  (c₁  , zlo) ← pair⇑ (addCarryU64 c₀ xlo ylo)
  (c₂  , zhi) ← pair⇑ (addCarryU64 c₁ xhi yhi)
  return (mkPair c₂ (mkPair zhi zlo))

-- we reuse `addCarryU128` as a stress-test for dead-code elimination
addTruncU128 : Tm U128 -> Tm U128 -> Tm U128
addTruncU128 x y = snd (addCarryU128 zeroBit x y)

addU64toU128 : Tm U64 -> Tm U128 -> Tm U128
addU64toU128 small big = addTruncU128 (smallU128 small) big

addU64toU64 : Tm U64 -> Tm U64 -> Tm U128
addU64toU64 x y = runGen do
  (c , lo) <- pair⇑ (addCarryU64 zeroBit x y)
  let hi = castBitU64 c
  return (mkPair hi lo)

--------------------------------------------------------------------------------

shiftLeftU128-by1 : Tm Bit -> Tm U128 -> Tm (Pair Bit U128)
shiftLeftU128-by1 c₀ input = runGen do
  (hi , lo ) <- pair⇑ input
  (c₁ , lo') <- pair⇑ (rotLeftU64 c₀ lo)
  (c₂ , hi') <- pair⇑ (rotLeftU64 c₁ hi)
  return (mkPair c₂ (mkPair hi lo))
  
shiftRightU128-by1 : Tm Bit -> Tm U128 -> Tm (Pair Bit U128)
shiftRightU128-by1 c₀ input = runGen do
  (hi , lo ) <- pair⇑ input
  (c₁ , hi') <- pair⇑ (rotRightU64 c₀ hi)
  (c₂ , lo') <- pair⇑ (rotRightU64 c₁ lo)
  return (mkPair c₂ (mkPair hi lo))

--------------------------------------------------------------------------------

sumU64 : List (Tm U64) -> Tm U128
sumU64 []          = zeroU128 
sumU64 (tm₁ ∷ tms) = go (smallU128 tm₁) tms where
  go : Tm U128 -> List (Tm U64) -> Tm U128
  go acc []       = acc
  go acc (u ∷ us) = go (addU64toU128 u acc) us

--------------------------------------------------------------------------------
