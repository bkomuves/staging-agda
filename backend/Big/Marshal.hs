
-- marshalling to/from bigint values (useful for debugging)

module Big.Marshal where

--------------------------------------------------------------------------------

import AST.Val
import Big.Limbs

--------------------------------------------------------------------------------

limbsToBigIntVal :: Limbs -> Val
limbsToBigIntVal limbs = WrapV name (StructV (map U64V limbs)) where
  name = "BigInt" ++ show (length limbs)

limbsFromBigIntVal_ :: [Val] -> Limbs
limbsFromBigIntVal_ = go where
  go []              = []
  go (U64V w : rest) = w : go rest
  go _               = error "limbsFromBigInt_: expecting a list of U64 values"

limbsFromBigIntVal :: Val -> Limbs
limbsFromBigIntVal (WrapV name (StructV vals)) 
  | name /= ref_name = error "limbsFromBigInt: wrong newtype"
  | otherwise        = limbsFromBigIntVal_ vals
  where
    ref_name = "BigInt" ++ show (length vals)

--------------------------------------------------------------------------------

integerToBigIntVal :: NLimbs -> Integer -> Val
integerToBigIntVal nlimbs n = limbsToBigIntVal (integerToLimbs nlimbs n)

integerFromBigIntVal :: Val -> Integer
integerFromBigIntVal = integerFromLimbs . limbsFromBigIntVal

--------------------------------------------------------------------------------

showBigIntVal :: Val -> String
showBigIntVal = show . integerFromBigIntVal

printBigIntVal :: Val -> IO ()
printBigIntVal = putStrLn . showBigIntVal

--------------------------------------------------------------------------------
