
module Aux.Misc where

--------------------------------------------------------------------------------

import Data.Word

import Debug.Trace

--------------------------------------------------------------------------------

debug s x y = trace (">>> " ++ s ++ " -> " ++ show x) y

--------------------------------------------------------------------------------

type Bit = Bool

zeroBit = False
oneBit  = True

bitToWord64 :: Bit -> Word64
bitToWord64 False = 0
bitToWord64 True  = 1

--------------------------------------------------------------------------------

safeZip :: [a] -> [b] -> [(a,b)]
safeZip = safeZipWith (,)

safeZipWith :: (a -> b -> c) -> [a] -> [b] -> [c] 
safeZipWith f = go where
  go []     []     = []
  go (x:xs) (y:ys) = f x y : go xs ys
  go _      _      = error "safeZipWith: inputs have different lengths"

--------------------------------------------------------------------------------

pairs :: [a] -> [(a,a)]
pairs []  = []
pairs [_] = []
pairs (x:y:rest) = (x,y) : pairs (y:rest)

--------------------------------------------------------------------------------
