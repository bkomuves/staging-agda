
-- primop semnatics

module Run.Semantics where

--------------------------------------------------------------------------------

import Data.Bits
import Data.Word
import Data.List

import Aux.Misc
import Big.Limbs

--------------------------------------------------------------------------------

-- | This is normally a CPU instruction
addCarry64 :: Bit -> Word64 -> Word64 -> (Bit,Word64)
addCarry64 carry x y = (carry',z) where
  res    = fromIntegral x + fromIntegral y + fromIntegral (bitToWord64 carry) :: Integer
  z      = fromInteger (res .&. limbMask)
  carry' = shiftR res limbSize > 0 

subCarry64 :: Bit -> Word64 -> Word64 -> (Bit,Word64)
subCarry64 carry x y = (carry',z) where
  res    = fromIntegral x - fromIntegral y - fromIntegral (bitToWord64 carry) :: Integer
  z      = fromInteger (res .&. limbMask)
  carry' = res < 0 

--------------------------------------------------------------------------------

shiftLeft64 :: Int -> Word64 -> Word64 
shiftLeft64 k x = shiftL x k .&. limbMask64

shiftRight64 :: Int -> Word64 -> Word64 
shiftRight64 k x = shiftR x k

rotLeftU64  :: Bit -> Word64 -> (Bit, Word64)
rotLeftU64 cin x = (cout, y) where
  cout = (x .&. msbMask64) > 0
  y    = shiftL x 1 .|. (if cin then 1 else 0)

rotRightU64 :: Bit -> Word64 -> (Bit, Word64)
rotRightU64 cin x = (cout, y) where
  cout = (x .&. 1) > 0
  y    = shiftR x 1 .|. (if cin then msbMask64 else 0)

--------------------------------------------------------------------------------

mulExtU64 :: Word64 -> Word64 -> (Word64, Word64)
mulExtU64 x y = (hi,lo) where
  z  = fromIntegral x * fromIntegral y :: Integer
  lo = fromInteger (z .&. limbMask)
  hi = fromInteger (shiftR z limbSize)

mulAddU64 :: Word64 -> Word64 -> Word64 -> (Word64, Word64)
mulAddU64 a x y = (hi,lo) where
  z  = fromIntegral a + fromIntegral x * fromIntegral y :: Integer
  lo = fromInteger (z .&. limbMask)
  hi = fromInteger (shiftR z limbSize)

--------------------------------------------------------------------------------

-- 64-bit comparisons
primEqU64 :: Word64 -> Word64 -> Bool
primEqU64 = (==)

primLtU64 :: Word64 -> Word64 -> Bool
primLtU64 = (<)

primLeU64 :: Word64 -> Word64 -> Bool
primLeU64 = (<=)

--------------------------------------------------------------------------------
-- bits

primCastBitU64 :: Bit -> Word64
primCastBitU64 False = 0
primCastBitU64 True  = 1

{-

primNot :: Bit -> Bit
primNot = not

primAnd :: Bit -> Bit -> Bit
primAnd = (&&)

primOr :: Bit -> Bit -> Bit
primOr = (||)

iFTE :: Bool -> a -> a -> a
iFTE cond x y = if cond then x else y

-}

--------------------------------------------------------------------------------

