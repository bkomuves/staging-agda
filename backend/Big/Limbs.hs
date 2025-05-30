
module Big.Limbs where

--------------------------------------------------------------------------------

import Data.Bits
import Data.Word
import Data.List

import Aux.Misc

--------------------------------------------------------------------------------

type NLimbs  = Int
type Limbs   = [Word64]

-- | At most 64
-- 
-- Using a small limb, say 3 bits, can be useful for testing 
-- (high chance for corner cases to appear)
limbSize :: Int
limbSize = 64 -- 5 

twiceLimbSize :: Int
twiceLimbSize = 2 * limbSize

limbMask :: Integer
limbMask = 2^limbSize - 1

limbMask64 :: Word64
limbMask64 = fromInteger limbMask

msbMask :: Integer
msbMask = 2^(limbSize - 1)

msbMask64 :: Word64
msbMask64 = fromInteger msbMask

--------------------------------------------------------------------------------

safeReduceLimbsTo :: NLimbs -> Limbs -> Limbs
safeReduceLimbsTo k input
  | all (==0) (drop k input)  = take k input
  | otherwise                 = error "safeReduceLimbsTo: does not fit"

requiredNumberOfLimbs :: Integer -> NLimbs
requiredNumberOfLimbs n = go 0 n where
  go cnt 0 = cnt
  go cnt k = go (cnt+1) (shiftR k limbSize)

integerToLimbs :: NLimbs -> Integer -> Limbs
integerToLimbs nlimbs = go nlimbs where
  go 0 0 = []
  go 0 _ = error $ "integerToLimbs: does not fit into " ++ show nlimbs ++ " limbs"
  go k n = fromInteger (n .&. limbMask) : go (k-1) (shiftR n limbSize)

integerToLimbsAsRequired :: Integer -> Limbs
integerToLimbsAsRequired = go where
  go 0 = []
  go n = fromInteger (n .&. limbMask) : go (shiftR n limbSize)

integerFromLimbs :: Limbs -> Integer
integerFromLimbs = go where
  go []     = 0
  go (x:xs) = fromIntegral x + shiftL (go xs) limbSize

--------------------------------------------------------------------------------
