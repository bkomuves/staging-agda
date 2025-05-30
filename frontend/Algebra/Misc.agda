
module Algebra.Misc where

--------------------------------------------------------------------------------

open import Data.Bool
open import Data.Nat
open import Data.Word64

--------------------------------------------------------------------------------

twoTo64 : ℕ
twoTo64 = 0x10000000000000000

--------------------------------------------------------------------------------

eqWord64 : Word64 -> Word64 -> Bool
eqWord64 = _==_

negWord64 : Word64 -> Word64
negWord64 x = fromℕ (twoTo64 ∸ toℕ x)

addWord64 : Word64 -> Word64 -> Word64
addWord64 x y = fromℕ (toℕ x + toℕ y)

mulWord64 : Word64 -> Word64 -> Word64
mulWord64 x y = fromℕ (toℕ x * toℕ y)

--------------------------------------------------------------------------------

data Half : Set where
  Even : ℕ -> Half
  Odd  : ℕ -> Half

{-
-- TOO SLOW
halve : ℕ -> Half
halve zero     = Even zero
halve (suc n₁) with halve n₁
halve _ | Even h = Odd h
halve _ | Odd  h = Even (suc h)
-}

halve : ℕ -> Half
halve n with n / 2
halve n | k with n % 2
halve n | k | zero = Even k
halve n | k | _    = Odd  k

{-# TERMINATING #-}
powWord64 : ℕ -> Word64 -> Word64
powWord64 = go where
  go : ℕ -> Word64 -> Word64
  go 0 _ = fromℕ 1
  go 1 x = x
  go n x with halve n 
  go _ x | Even k = let y = go k x in            mulWord64 y y
  go _ x | Odd  k = let y = go k x in mulWord64 (mulWord64 y y) x

--------------------------------------------------------------------------------

{-
ex1 : Word64
ex1 = powWord64 50 (fromℕ 3)

ex2 : Word64
ex2 = powWord64 500 (fromℕ 3)

ex3 : Word64
ex3 = powWord64 5000 (fromℕ 3)

ex4 : Word64
ex4 = powWord64 50000 (fromℕ 3)
-}

