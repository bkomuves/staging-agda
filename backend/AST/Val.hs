
{-# LANGUAGE GADTSyntax, GeneralizedNewtypeDeriving, PatternSynonyms #-}
module AST.Val where

--------------------------------------------------------------------------------

import Data.Word
import Text.Read

import AST.Ty
-- import Big.Limbs

--------------------------------------------------------------------------------

 -- used only for the evaluator
data Function 
  = MkFun (Val -> Val)

instance Eq   Function where (==)     = error "Function/Eq"
instance Show Function where show     = error "Function/Show"
instance Read Function where readPrec = error "Function/Read"

--------------------------------------------------------------------------------

data Val where
  Tt      ::                  Val
  BitV    :: Bool          -> Val
  U64V    :: Word64        -> Val
  NatV    :: Integer       -> Val
  StructV :: [Val]         -> Val
  WrapV   :: String -> Val -> Val
  FunV    :: Function      -> Val      -- ^ used only for the evaluator

deriving instance Eq   Val
deriving instance Show Val
deriving instance Read Val

--------------------------------------------------------------------------------

pattern PairV x y = StructV [x,y]

--------------------------------------------------------------------------------

valTy :: Val -> Ty
valTy val = case val of
  Tt          -> Unit
  BitV _      -> Bit
  U64V _      -> U64
  NatV _      -> Nat
  StructV xs  -> Struct (map valTy xs)
  WrapV   n x -> Named n (valTy x)
  FunV {}     -> error "valTy: FunV"

--------------------------------------------------------------------------------
