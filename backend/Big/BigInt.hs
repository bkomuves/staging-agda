
-- | BigInt algorithms
--
-- This is for clarity of understanding the algorithms
---

module Big.BigInt where

--------------------------------------------------------------------------------

import Data.Bits
import Data.Word
import Data.List

-- import Control.Monad
-- import System.Random

import AST.Semantics
import Big.Limbs
import Aux.Misc

--------------------------------------------------------------------------------

zeroBigInt :: NLimbs -> Limbs
zeroBigInt n = replicate n 0

smallBigInt :: NLimbs -> Word64 -> Limbs
smallBigInt n x = x : replicate (n-1) 0

--------------------------------------------------------------------------------
-- *** ADDITION ***

addBigInt :: Bit -> Limbs -> Limbs -> (Bit,Limbs)
addBigInt carry as bs = mapAccumL f carry (safeZip as bs) where
  f c (x,y) = addCarry64 c x y

subBigInt :: Bit -> Limbs -> Limbs -> (Bit,Limbs)
subBigInt carry as bs = mapAccumL f carry (safeZip as bs) where
  f c (x,y) = subCarry64 c x y

addBigInt_ :: Limbs -> Limbs -> Limbs
addBigInt_ xs ys = snd $ addBigInt zeroBit xs ys

subBigInt_ :: Limbs -> Limbs -> Limbs
subBigInt_ xs ys = snd $ subBigInt zeroBit xs ys

--------------------------------------------------------------------------------
-- *** COMPARISON ***

cmpBigInt :: Limbs -> Limbs -> Ordering
cmpBigInt xs ys 
  | length xs /= length ys  = error "cmpBigInt: incompatible inputs"
  | otherwise               = go (reverse xs) (reverse ys)
  where
    go []     []     = EQ
    go (x:xs) (y:ys) = case compare x y of
      LT -> LT
      GT -> GT
      EQ -> go xs ys

ltBigInt :: Limbs -> Limbs -> Bool
ltBigInt xs ys = case cmpBigInt xs ys of
  LT -> True
  EQ -> False
  GT -> False

leBigInt :: Limbs -> Limbs -> Bool
leBigInt xs ys = case cmpBigInt xs ys of
  LT -> True
  EQ -> True
  GT -> False

gtBigInt :: Limbs -> Limbs -> Bool
gtBigInt xs ys = not (leBigInt xs ys)

geBigInt :: Limbs -> Limbs -> Bool
geBigInt xs ys = not (ltBigInt xs ys)

--------------------------------------------------------------------------------
--- *** SHIFTS ***

smallShlBigInt :: Int -> Limbs -> Limbs
smallShlBigInt k xs
  | k <  0         = error "smallShlBigInt: negative shift amount"
  | k >= limbSize  = error "smallShlBigInt: shift larger or equal than limb size"
  | k == 0         = xs
  | otherwise      = [ shiftLeft64 k v .|.  shiftRight64 (limbSize - k) u | (u,v) <- pairs (0:xs) ]

smallShrBigInt :: Int -> Limbs -> Limbs
smallShrBigInt k xs
  | k <  0         = error "smallShrBigInt: negative shift amount"
  | k >= limbSize  = error "smallShrBigInt: shift larger or equal than limb size"
  | k == 0         = xs
  | otherwise      = [ shiftRight64 k u .|. shiftLeft64 (limbSize - k) v | (u,v) <- pairs (xs++[0]) ]

shlBigInt :: Int -> Limbs -> Limbs
shlBigInt k xs
  | k < 0     = error "shlBigInt: negative shift amount" 
  | otherwise = case divMod k limbSize of
      (q,r) -> if q >= nlimbs
        then replicate nlimbs 0
        else replicate q 0 ++ smallShlBigInt r (take (nlimbs - q) xs)
  where
    nlimbs = length xs

shrBigInt :: Int -> Limbs -> Limbs
shrBigInt k xs
  | k < 0     = error "shrBigInt: negative shift amount" 
  | otherwise = case divMod k limbSize of
      (q,r) -> if q >= nlimbs
        then replicate nlimbs 0
        else smallShrBigInt r (drop q xs) ++ replicate q 0
  where
    nlimbs = length xs

--------------------------------------------------------------------------------
--- *** 128 BITS ***

data Word128 
  = Word128 { hi :: !Word64 , lo :: !Word64 }
  deriving (Eq,Show)

deconstructWord128 :: Word128 -> (Word64,Word64)
deconstructWord128 (Word128 hi lo) = (hi,lo)
 
-- | This is normally CPU instruction (sometimes 2, separate for hi and lo)
mulExt64 :: Word64 -> Word64 -> Word128
mulExt64 x y = Word128 hi lo where
  res = fromIntegral x * fromIntegral y :: Integer
  lo  = fromInteger (res .&. limbMask)
  hi  = fromInteger (shiftR res limbSize)

mulAdd64 :: Word64 -> (Word64,Word64) -> Word128
mulAdd64 a (x,y) = Word128 hi lo where
  (Word128 hi0 lo0) = mulExt64 x y
  (c,lo) = addCarry64 zeroBit a lo0
  (_,hi) = addCarry64 c       0 hi0

-- | This is normally CPU instruction (on Intel at least. Apparently doesn't exist on ARM...)
-- 
-- and on Intel it throws an exception when the result overflows
div128 :: Word128 -> Word64 -> Word64
div128 (Word128 num_hi num_lo) denom 
  | q <= limbMask  = fromInteger q
  | otherwise      = error "div128: overflow"
  where
    q = (2^limbSize * fromIntegral num_hi + fromIntegral num_lo) `div` (fromIntegral denom) :: Integer

le128 :: Word128 -> Word128 -> Bool
le128 (Word128 ahi alo) (Word128 bhi blo) = case compare ahi bhi of
  LT -> True
  EQ -> alo <= blo
  GT -> False

lt128 :: Word128 -> Word128 -> Bool
lt128 (Word128 ahi alo) (Word128 bhi blo) = case compare ahi bhi of
  LT -> True
  EQ -> alo < blo
  GT -> False

--------------------------------------------------------------------------------

sumWord64 :: [Word64] -> Word128
sumWord64 []     = Word128 0 0 
sumWord64 (x:xs) = foldl f (Word128 0 x) xs where
  f (Word128 hi lo) x = Word128 hi' lo' where
    (c,lo') = addCarry64 zeroBit lo x
    hi'     = if c then hi+1 else hi

--------------------------------------------------------------------------------

addCarry128 :: Bit -> Word128 -> Word128 -> (Bit,Word128)
addCarry128 c0 (Word128 hi1 lo1) (Word128 hi2 lo2) = (c2, Word128 hi3 lo3) where
  (c1,lo3) = addCarry64 c0 lo1 lo2
  (c2,hi3) = addCarry64 c1 hi1 hi2

subCarry128 :: Bit -> Word128 -> Word128 -> (Bit,Word128)
subCarry128 c0 (Word128 hi1 lo1) (Word128 hi2 lo2) = (c2, Word128 hi3 lo3) where
  (c1,lo3) = subCarry64 c0 lo1 lo2
  (c2,hi3) = subCarry64 c1 hi1 hi2

sumWord128 :: [Word128] -> (Word64,Word128)
sumWord128 []     = (0, Word128 0 0) 
sumWord128 (x:xs) = foldl f (0, x) xs where
  f :: (Word64,Word128) -> Word128 -> (Word64,Word128)
  f (hi, lo) x = (hi', lo') where
    (c,lo') = addCarry128 zeroBit lo x
    hi'     = if c then hi+1 else hi

--------------------------------------------------------------------------------
-- *** MULTIPLICATION ***

scaleBigInt :: Word64 -> Limbs -> Limbs
scaleBigInt s as = (go 0 as) where
  go carry []     = [carry] 
  go carry (a:as) = case mulAdd64 carry (s,a) of
    Word128 hi lo -> lo : go hi as

mulBigInt :: Limbs -> Limbs -> Limbs
mulBigInt = mulV1

-- versiomn using 64 bit additions
mulV1 :: Limbs -> Limbs -> Limbs
mulV1 a b = safeReduceLimbsTo (n+m) $ result where
  n = length a
  m = length b

  tmp :: [ ([Word64] , [Word64]) ]
  tmp = [ unzip
            [ deconstructWord128 $ mulExt64 (a!!i) (b!!j) 
            | i<-[0..k] 
            , let j = k-i
            , i < n
            , j < m
            ]
        | k<-[0..n+m-2]
        ]

  almost :: [Word128]
  almost = map sumWord64 $ flattenHiLo (++) tmp

  (False, result) = foldHiLo 0 addCarry64 zeroBit $ map deconstructWord128 almost


--------------------------------------------------------------------------------

{-
-- version using 128 bit additions
mulV2 :: Limbs -> Limbs -> Limbs
mulV2 a b = result where
  n = length a
  m = length b
  tmp :: [(Word64,Word128)]
  tmp = 
    [ sumWord128
         [ mulExt64 (a!!i) (b!!j) 
         | i<-[0..k-1] 
         , let j = k-i
         , i < n
         , j < m
         ]
     | k<-[0..n+m-1]
     ]

  tmp' = [ (c,hi,lo) | (c, Word128 hi lo) <- tmp ]
-}

--------------------------------------------------------------------------------

-- | Try this to get an illustration what this does:
--
-- > flattenHiLo (+) $ zip [100,200..500] [1..5] 
--
flattenHiLo :: (a -> a -> a) -> [(a,a)] -> [a]
flattenHiLo f = go Nothing where
  go Nothing  []           = []
  go (Just y) []           = [y]
  go mbPrev ((hi,lo):rest) = case mbPrev of
    Nothing   ->        lo : go (Just hi) rest 
    Just prev -> f prev lo : go (Just hi) rest

foldHiLo :: a -> (s -> a -> a -> (s,a)) -> s ->  [(a,a)] -> (s,[a])
foldHiLo zero f s0 = go s0 zero where
  go s prev []             = let (s' , y ) = f s prev zero 
                             in  (s' ,[y])
  go s prev ((hi,lo):rest) = let (s' , y ) = f s prev lo  
                                 (s'', ys) = go s' hi rest 
                             in  (s'', y:ys)

--------------------------------------------------------------------------------
-- *** DIVISION ***

-- | See:
--
-- * Handbook of Applied Cryptography
--
-- * Brent and Zimmermann: Modern Computer Arithmetic
--
divRemBigInt :: Limbs -> Limbs -> (Limbs,Limbs)
divRemBigInt as0 bs0 = (qs, shrBigInt shiftSmall rs) where
    (qs,rs) = divRemNormalizedBigInt as bs

    -- normalize
    (shiftWord,shiftSmall) = findDivNormalizationShift bs0
    as = shlBigInt shiftSmall $ as0 ++ [0]
    bs = shlBigInt shiftSmall $ take (m0 - shiftWord) bs0
    m0 = length bs0

-- | Assumes that denominator is normalized (most significant bit is 1)
divRemNormalizedBigInt :: Limbs -> Limbs -> (Limbs,Limbs)
divRemNormalizedBigInt as0 bs
  | bmsb /= msb_mask  = error "divRemNormalizedBigInt: denominator is not normalized"
  | d < 0             = ([], as0)
  | otherwise         = (qs, rs) 
  where

    n = length as0
    m = length bs
    d = n - m
  
    -- ensure that `A < B * beta^d`
    (qd,as1) = case subBigInt zeroBit as0 (replicate d 0 ++ bs) of
      (True,  _  ) -> (0,as0)
      (False, as') -> (1,as')

    (qs, rs) = worker (d-1) [qd] as1

    msb_mask = 2^(limbSize - 1)
    bmsb = btop .&. msb_mask
    btop = last bs
    -- b128 = (2^limbSize-1) * btop = maximum numerator
    (False,b128) = subCarry128 zeroBit (Word128 btop 0) (Word128 0 btop)   

    worker j qs as 
      | j < 0     = (qs,as)
      | otherwise = worker (j-1) (q':qs) as'
      where
        a128 = Word128 (as!!(m+j)) (as!!(m+j-1))
        qj   = if a128 `lt128` b128 then div128 a128 btop else limbMask64
        (c1,as1) = subBigInt zeroBit as (replicate j 0 ++ scaleBigInt qj bs ++ replicate (d-j-1) 0)
        (q',as') = if not c1 
          then (qj,as1)
          else let (c2,as2) = addBigInt zeroBit as1 (replicate j 0 ++ bs ++ replicate (d-j) 0)
               in  if c2
                 then (qj-1,as2)
                 else let (c3,as3) = addBigInt zeroBit as2 (replicate j 0 ++ bs ++ replicate (d-j) 0)
                      in if c3 
                        then (qj-2,as3)
                        else error "divRemNormalizedBigInt: shouldn't happen"

-- finds the left shift necessary so that the most significant bit is 1
-- returns `(q,r)` where `q` is the number of full limb shifts and `0 <= r < limbSize` is the remaining bitshift
findDivNormalizationShift :: Limbs -> (Int,Int)
findDivNormalizationShift bs0 = (wordcnt,bitcnt) where

  (wordcnt,b0) = go1 0 (reverse bs0)
  go1 cnt [] = error "findDivNormalizationShift: input is zero"
  go1 cnt (b:bs) = if b == 0 
    then go1 (cnt+1) bs 
    else (cnt, b)

  msbmask = 2^(limbSize - 1) :: Word64 
  bitcnt = go 0 b0
  go !cnt x = if (x .&. msbmask) /= 0 
    then cnt
    else go (cnt+1) (shiftL x 1)

--------------------------------------------------------------------------------
